//! #1145 / #406 (RQ-89-MEMLAYER6): per-memory layering of the
//! `--native-pointer-abi` static-data classification.
//!
//! ## The ABI this layers
//!
//! Under `--native-pointer-abi` MEMORY 0 is native: R11 is 0, a wasm static
//! at offset `C` lives at `__synth_wasm_data + C`, and the selector rewrites
//! two kinds of VALUE into that native form before any access sees them:
//!
//! 1. an `i32.const C` inside memory 0's static window
//!    `[sp_init, memory-0 bytes)` (the #237 rule, keyed on the stack-pointer
//!    global), and
//! 2. every read of the stack-pointer global (rebased by `__synth_wasm_data`;
//!    its writes are rebased back).
//!
//! MEMORY k > 0 is NOT native on any path: an access to memory k is
//! `__synth_wasm_data_<k> + addr` (the VCR-MEM-002 phase-1 lowering), so a
//! value used as a memory-k address must stay a raw wasm OFFSET. That is the
//! downstream contract recorded on #1145 (memory 0 native, memory k at exact
//! wasm offsets through the region table), and it is also what keeps the
//! memory-k lowering byte-identical to the non-NPA multi-memory path.
//!
//! The phase-1 refusal existed because the rewrite happens on the VALUE,
//! before any access knows its memory: a memory-1 static constant that sits
//! inside memory 0's window was rewritten to `__synth_wasm_data + C` and then
//! added to `__synth_wasm_data_1` (RQ-88-MEMLAYER5, executed: `read1_static`
//! returned 0x0 where wasmtime returns 0xaaaaaaaa).
//!
//! ## What this pass computes
//!
//! A module-level, flow-insensitive, field-insensitive value-provenance
//! analysis: for every value node, the set of memories it may be used as an
//! ADDRESS in. Nodes are each pushed value, every local / parameter, every
//! function result, every global, and one node per memory standing for "any
//! value stored in that memory" (a pointer laundered through memory is
//! therefore tracked, conservatively). Flow edges cover locals, globals,
//! direct calls, `call_indirect` (to every arity-matching element-segment
//! target), returns, block/branch results, `select`, stores→loads per memory,
//! and arithmetic (a result derives from all of its operands). Comparisons and
//! subtraction additionally COUPLE their operands (both must be in one
//! representation for the result to mean what wasm says), so taint flows both
//! ways across them.
//!
//! The taint is an over-approximation by construction: anything the pass
//! cannot model (an unmodeled op, an unknown block arity, a stack underflow)
//! is an error, never a guess. The decision rule then only ever turns
//! imprecision into a LOUD refusal:
//!
//! * a rewritable source (an `i32.const` in memory 0's window, or the chosen
//!   stack-pointer global) that may reach a memory-k address and NOT a
//!   memory-0 address is left RAW — it is a memory-k offset, which is exactly
//!   what wasm computes and what the memory-k lowering adds its base to;
//! * one that may reach BOTH is refused (no single representation is right);
//! * the stack-pointer global is chosen only among candidates that never
//!   reach a memory-k address (a `meld --domain` module carries one stack
//!   pointer per domain; picking memory 1's would rebase it into memory 0).
//!
//! Host boundaries (import arguments, export parameters/results, imported or
//! loud-skipped callees) carry each memory's own representation: memory-0
//! pointers native, memory-k pointers as wasm offsets — the same contract
//! the region table (`__synth_mem_base_N`) already documents for memory k.
//!
//! Single-memory modules never reach this pass (the CLI gates it on more than
//! one memory), so every single-memory object is byte-identical by
//! construction.

use std::collections::HashMap;

use crate::wasm_op::WasmOp;
use crate::wasm_stack_check::fixed_stack_effect;

/// One function as the pass sees it.
pub struct NpaFunc<'a> {
    /// Full wasm function index (imports first).
    pub index: u32,
    pub ops: &'a [WasmOp],
    /// The decoder's ordinal blocktype-arity side table (#509).
    pub block_arity: &'a [(u8, u8)],
    pub param_count: u32,
    pub result_count: u32,
    /// Exported: its parameters arrive from the host.
    pub exported: bool,
}

/// The module-level inputs.
pub struct NpaModule<'a> {
    /// Every DEFINED function whose op stream is complete. A function the
    /// decoder flagged unsupported is loud-skipped by the compile (its symbol
    /// is left undefined for the host), so it is modeled like an import.
    pub funcs: Vec<NpaFunc<'a>>,
    pub num_imported_funcs: u32,
    /// Parameter count per full function index.
    pub func_arg_counts: &'a [u32],
    /// Result count per full function index.
    pub func_result_counts: &'a [u32],
    pub type_arg_counts: &'a [u32],
    pub type_result_counts: &'a [u32],
    /// Every function index placed in a table by an element segment — the
    /// possible `call_indirect` targets.
    pub elem_func_indices: &'a [u32],
    /// Number of linear memories (defined + imported).
    pub memory_count: u32,
    /// `--embedder-copies-carry-no-pointers`: the caller ASSERTS that a
    /// cross-memory `memory.copy` never carries a value later used as an
    /// address in the destination memory (the Canonical-ABI property), so
    /// such a copy does not join the two memories' contents. A same-memory
    /// copy and every other route are tracked unchanged.
    pub cross_copies_carry_no_pointers: bool,
}

type Node = usize;

/// Bit `m` set ⇔ the value may be used as an address in memory `m`.
type Mask = u32;

#[derive(Default)]
struct Graph {
    /// `preds[v]` = every node whose value flows into `v`.
    preds: Vec<Vec<Node>>,
    /// Direct address uses.
    taint: Vec<Mask>,
    locals: HashMap<(u32, u32), Node>,
    rets: HashMap<(u32, u32), Node>,
    globals: HashMap<u32, Node>,
    mems: HashMap<u32, Node>,
    /// `(function index, op index)` of every `i32.const` → its node.
    consts: HashMap<(u32, usize), (i32, Node)>,
    /// Values the HOST supplies: `(what, node)` for each exported function's
    /// parameters and each import call's results.
    host_entries: Vec<(String, Node)>,
    /// A cross-memory copy joined two memories' contents.
    joined_by_cross_copy: bool,
    /// RQ-91-NPAMODEL: the memory-0 facts the native-pointer decision
    /// ([`Provenance::memory0_plan`]) reads. Recorded by the same walk.
    m0: M0Facts,
}

/// RQ-91-NPAMODEL: what the walk records for the memory-0 decision, beside
/// the reach graph. `fpreds` are the DIRECTED value flows only — `preds`
/// also carries the two-way coupling of comparisons and subtraction (the
/// #1145 reach rule), which must not make a compared constant look like an
/// operand of the address it is compared with.
#[derive(Default)]
struct M0Facts {
    fpreds: Vec<Vec<Node>>,
    /// Memory-0 accesses, in walk order.
    accesses: Vec<M0Access>,
    /// `(result, lhs, rhs, is_sub)` of every `i32.add` / `i32.sub`.
    binops: Vec<(Node, Node, Node, bool)>,
    /// Value nodes whose constant value set is unknown (an arithmetic result
    /// other than add/sub, a load, a global, a host value).
    opaque: std::collections::HashSet<Node>,
    /// Load results (memory 0): they read memory content, so a constant
    /// stored there is NOT a direct operand of the address the loaded value
    /// later forms. `(result, memory content node)`.
    load_results: HashMap<Node, Node>,
    /// Values consumed as a SCALAR: a comparison operand, a branch or select
    /// condition, an operand of arithmetic other than add/sub, an argument to
    /// or a result returned to the host.
    observed: Vec<Node>,
    /// Values that leave the module (export results, import arguments).
    host_exits: Vec<Node>,
    /// Memory-0 stores `(address, value)` — `memory.fill` included, its
    /// fill value as the stored value.
    stores: Vec<(Node, Node)>,
    /// Memory-0 `memory.copy` `(destination, source)`.
    copies: Vec<(Node, Node)>,
    /// The implicit zero of a non-parameter local read before any set that
    /// provably precedes it: `(function, local, node)`.
    zero_inits: Vec<(u32, u32, Node)>,
}

/// One memory-0 access as the walk saw it.
#[derive(Clone)]
struct M0Access {
    func: u32,
    op: usize,
    addr: Node,
    offset: u32,
    /// Access width; `None` for a bulk op (the length is `len`).
    width: Option<u32>,
    len: Option<Node>,
    what: &'static str,
    /// A `memory.copy` source (read) side.
    is_copy_src: bool,
    /// A load: its result node.
    result: Option<Node>,
}

impl Graph {
    fn fresh(&mut self) -> Node {
        self.preds.push(Vec::new());
        self.taint.push(0);
        self.m0.fpreds.push(Vec::new());
        self.preds.len() - 1
    }
    fn keyed<K: std::hash::Hash + Eq>(
        map: &mut HashMap<K, Node>,
        k: K,
        g: &mut Vec<Vec<Node>>,
        t: &mut Vec<Mask>,
        f: &mut Vec<Vec<Node>>,
    ) -> Node {
        *map.entry(k).or_insert_with(|| {
            g.push(Vec::new());
            t.push(0);
            f.push(Vec::new());
            g.len() - 1
        })
    }
    fn local(&mut self, f: u32, l: u32) -> Node {
        Self::keyed(
            &mut self.locals,
            (f, l),
            &mut self.preds,
            &mut self.taint,
            &mut self.m0.fpreds,
        )
    }
    fn ret(&mut self, f: u32, r: u32) -> Node {
        Self::keyed(
            &mut self.rets,
            (f, r),
            &mut self.preds,
            &mut self.taint,
            &mut self.m0.fpreds,
        )
    }
    fn global(&mut self, g: u32) -> Node {
        Self::keyed(
            &mut self.globals,
            g,
            &mut self.preds,
            &mut self.taint,
            &mut self.m0.fpreds,
        )
    }
    fn mem(&mut self, m: u32) -> Node {
        Self::keyed(
            &mut self.mems,
            m,
            &mut self.preds,
            &mut self.taint,
            &mut self.m0.fpreds,
        )
    }
    /// The value of `from` flows into `to`.
    fn flow(&mut self, from: Node, to: Node) {
        if from != to {
            self.preds[to].push(from);
            self.m0.fpreds[to].push(from);
        }
    }
    /// `a` and `b` must share one representation.
    fn couple(&mut self, a: Node, b: Node) {
        if a != b {
            self.preds[b].push(a);
            self.preds[a].push(b);
        }
    }
    fn observe(&mut self, n: Node) {
        self.m0.observed.push(n);
    }
    fn address(&mut self, n: Node, memory: u32) -> Result<(), String> {
        if memory >= 32 {
            return Err(format!(
                "memory index {memory} (the pass models memories 0..31)"
            ));
        }
        self.taint[n] |= 1 << memory;
        Ok(())
    }
    fn propagate(&mut self) {
        let mut work: Vec<Node> = (0..self.taint.len())
            .filter(|&n| self.taint[n] != 0)
            .collect();
        while let Some(v) = work.pop() {
            let t = self.taint[v];
            for i in 0..self.preds[v].len() {
                let u = self.preds[v][i];
                if self.taint[u] | t != self.taint[u] {
                    self.taint[u] |= t;
                    work.push(u);
                }
            }
        }
    }
}

/// The analysis result.
pub struct Provenance {
    graph: Graph,
}

/// Where a value may be dereferenced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reach(Mask);

impl Reach {
    /// May be used as a memory-0 address.
    pub fn memory0(self) -> bool {
        self.0 & 1 != 0
    }
    /// The memories > 0 it may be used as an address in.
    pub fn memories_k(self) -> Vec<u32> {
        (1..32).filter(|m| self.0 & (1 << m) != 0).collect()
    }
}

struct Frame {
    is_loop: bool,
    is_if: bool,
    saw_else: bool,
    height: usize,
    params: Vec<Node>,
    results: Vec<Node>,
    unreachable: bool,
}

impl Provenance {
    pub fn analyze(m: &NpaModule) -> Result<Provenance, String> {
        let mut g = Graph::default();
        let analyzed: std::collections::HashSet<u32> = m.funcs.iter().map(|f| f.index).collect();
        for f in &m.funcs {
            walk(&mut g, m, &analyzed, f).map_err(|e| format!("function {}: {e}", f.index))?;
        }
        g.propagate();
        Ok(Provenance { graph: g })
    }

    /// Reach of the `i32.const` at `(func, op)`, with its value.
    pub fn const_at(&self, func: u32, op: usize) -> Option<(i32, Reach)> {
        self.graph
            .consts
            .get(&(func, op))
            .map(|&(c, n)| (c, Reach(self.graph.taint[n])))
    }

    /// Every `i32.const` site: `(func, op, value, reach)`, sorted.
    pub fn consts(&self) -> Vec<(u32, usize, i32, Reach)> {
        let mut v: Vec<_> = self
            .graph
            .consts
            .iter()
            .map(|(&(f, i), &(c, n))| (f, i, c, Reach(self.graph.taint[n])))
            .collect();
        v.sort_by_key(|&(f, i, _, _)| (f, i));
        v
    }

    /// TRUE when a cross-memory copy joined two memories' contents — the
    /// join `--embedder-copies-carry-no-pointers` lifts.
    pub fn joined_by_cross_copy(&self) -> bool {
        self.graph.joined_by_cross_copy
    }

    /// Host-supplied values and their reach.
    pub fn host_entries(&self) -> Vec<(String, Reach)> {
        self.graph
            .host_entries
            .iter()
            .map(|(w, n)| (w.clone(), Reach(self.graph.taint[*n])))
            .collect()
    }

    /// Reach of global `g` (no node ⇒ never read or written ⇒ no reach).
    pub fn global(&self, g: u32) -> Reach {
        Reach(
            self.graph
                .globals
                .get(&g)
                .map(|&n| self.graph.taint[n])
                .unwrap_or(0),
        )
    }
}

fn walk(
    g: &mut Graph,
    m: &NpaModule,
    analyzed: &std::collections::HashSet<u32>,
    f: &NpaFunc,
) -> Result<(), String> {
    use WasmOp::*;
    let fi = f.index;
    let mut stack: Vec<Node> = Vec::new();
    let fn_results: Vec<Node> = (0..f.result_count).map(|r| g.ret(fi, r)).collect();
    if f.exported {
        g.m0.host_exits.extend(fn_results.iter().copied());
        for p in 0..f.param_count {
            let n = g.local(fi, p);
            g.host_entries
                .push((format!("parameter {p} of exported function {fi}"), n));
        }
    }
    let mut frames: Vec<Frame> = vec![Frame {
        is_loop: false,
        is_if: false,
        saw_else: false,
        height: 0,
        params: Vec::new(),
        results: fn_results.clone(),
        unreachable: false,
    }];
    let mut ordinal = 0usize;
    // RQ-91-NPAMODEL: a non-parameter local holds 0 until set. Its first
    // occurrence being a set at block depth 0 proves the set precedes every
    // read (code at depth 0 runs in order); otherwise the zero may be read.
    {
        let mut first: HashMap<u32, bool> = HashMap::new();
        let mut depth = 0i32;
        for op in f.ops {
            match op {
                Block | Loop | If => depth += 1,
                End => depth -= 1,
                LocalGet(l) if *l >= f.param_count => {
                    first.entry(*l).or_insert(false);
                }
                LocalSet(l) | LocalTee(l) if *l >= f.param_count => {
                    first.entry(*l).or_insert(depth == 0);
                }
                _ => {}
            }
        }
        let mut zero_reachable: Vec<u32> = first
            .into_iter()
            .filter_map(|(l, dominated)| (!dominated).then_some(l))
            .collect();
        zero_reachable.sort_unstable();
        for l in zero_reachable {
            let z = g.fresh();
            let ln = g.local(fi, l);
            g.flow(z, ln);
            g.m0.zero_inits.push((fi, l, z));
        }
    }

    fn pop(
        g: &mut Graph,
        stack: &mut Vec<Node>,
        frames: &[Frame],
        i: usize,
    ) -> Result<Node, String> {
        let fr = frames
            .last()
            .ok_or_else(|| format!("op {i}: no open control frame"))?;
        if stack.len() > fr.height {
            Ok(stack.pop().unwrap())
        } else if fr.unreachable {
            Ok(g.fresh())
        } else {
            Err(format!("op {i}: value-stack underflow"))
        }
    }
    fn pop_n(
        g: &mut Graph,
        stack: &mut Vec<Node>,
        frames: &[Frame],
        n: usize,
        i: usize,
    ) -> Result<Vec<Node>, String> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(pop(g, stack, frames, i)?);
        }
        v.reverse();
        Ok(v)
    }
    // The values a branch to label `l` carries flow into the label's slots.
    fn label_flow(
        g: &mut Graph,
        stack: &[Node],
        frames: &[Frame],
        l: u32,
        i: usize,
    ) -> Result<(), String> {
        let depth = frames.len();
        let target = depth
            .checked_sub(1 + l as usize)
            .and_then(|k| frames.get(k))
            .ok_or_else(|| format!("op {i}: branch label {l} out of range"))?;
        let slots = if target.is_loop {
            &target.params
        } else {
            &target.results
        };
        let top = frames.last().unwrap();
        let avail = stack.len().saturating_sub(top.height);
        if avail < slots.len() && !top.unreachable {
            return Err(format!(
                "op {i}: branch carries {} value(s) from a depth of {avail}",
                slots.len()
            ));
        }
        let n = slots.len().min(avail);
        let base = stack.len() - n;
        let skip = slots.len() - n;
        for k in 0..n {
            g.flow(stack[base + k], slots[skip + k]);
        }
        Ok(())
    }

    for (i, op) in f.ops.iter().enumerate() {
        // Memory index + inner op for a memory access.
        let (memory, inner): (u32, &WasmOp) = match op {
            MultiMemory { memory, op } => (*memory, op.as_ref()),
            other => (0, other),
        };
        match inner {
            Block | Loop | If => {
                let (p, r) = *f.block_arity.get(ordinal).ok_or_else(|| {
                    format!("op {i}: no blocktype arity for construct #{ordinal}")
                })?;
                ordinal += 1;
                if p == u8::MAX || r == u8::MAX {
                    return Err(format!("op {i}: unresolvable blocktype"));
                }
                if matches!(inner, If) {
                    let c = pop(g, &mut stack, &frames, i)?;
                    g.observe(c);
                }
                let vals = pop_n(g, &mut stack, &frames, p as usize, i)?;
                let params: Vec<Node> = vals
                    .iter()
                    .map(|&v| {
                        let n = g.fresh();
                        g.flow(v, n);
                        n
                    })
                    .collect();
                let results: Vec<Node> = (0..r).map(|_| g.fresh()).collect();
                let height = stack.len();
                stack.extend(params.iter().copied());
                frames.push(Frame {
                    is_loop: matches!(inner, Loop),
                    is_if: matches!(inner, If),
                    saw_else: false,
                    height,
                    params,
                    results,
                    unreachable: false,
                });
            }
            Else => {
                let n = frames.last().map(|fr| fr.results.len()).unwrap_or(0);
                let vals = pop_n(g, &mut stack, &frames, n, i)?;
                let fr = frames
                    .last_mut()
                    .ok_or_else(|| format!("op {i}: else without if"))?;
                for (k, v) in vals.into_iter().enumerate() {
                    g.flow(v, fr.results[k]);
                }
                stack.truncate(fr.height);
                stack.extend(fr.params.iter().copied());
                fr.unreachable = false;
                fr.saw_else = true;
            }
            End => {
                let n = frames.last().map(|fr| fr.results.len()).unwrap_or(0);
                let vals = pop_n(g, &mut stack, &frames, n, i)?;
                let fr = frames
                    .pop()
                    .ok_or_else(|| format!("op {i}: unbalanced end"))?;
                for (k, v) in vals.into_iter().enumerate() {
                    g.flow(v, fr.results[k]);
                }
                if fr.is_if && !fr.saw_else {
                    for (p, r) in fr.params.iter().zip(fr.results.iter()) {
                        g.flow(*p, *r);
                    }
                }
                stack.truncate(fr.height);
                if frames.is_empty() {
                    // The function body's own `end`.
                    if i + 1 != f.ops.len() {
                        return Err(format!("op {i}: ops after the function's end"));
                    }
                } else {
                    stack.extend(fr.results.iter().copied());
                }
            }
            Br(l) => {
                label_flow(g, &stack, &frames, *l, i)?;
                let fr = frames.last_mut().unwrap();
                stack.truncate(fr.height);
                fr.unreachable = true;
            }
            BrIf(l) => {
                let c = pop(g, &mut stack, &frames, i)?;
                g.observe(c);
                label_flow(g, &stack, &frames, *l, i)?;
            }
            BrTable { targets, default } => {
                let c = pop(g, &mut stack, &frames, i)?;
                g.observe(c);
                for l in targets.iter().chain(std::iter::once(default)) {
                    label_flow(g, &stack, &frames, *l, i)?;
                }
                let fr = frames.last_mut().unwrap();
                stack.truncate(fr.height);
                fr.unreachable = true;
            }
            Return => {
                let vals = pop_n(g, &mut stack, &frames, fn_results.len(), i)?;
                for (k, v) in vals.into_iter().enumerate() {
                    g.flow(v, fn_results[k]);
                }
                let fr = frames.last_mut().unwrap();
                stack.truncate(fr.height);
                fr.unreachable = true;
            }
            Unreachable => {
                let fr = frames.last_mut().unwrap();
                stack.truncate(fr.height);
                fr.unreachable = true;
            }
            Call(c) => {
                let argc = *m
                    .func_arg_counts
                    .get(*c as usize)
                    .ok_or_else(|| format!("op {i}: call {c} has no signature"))?;
                let resc = *m
                    .func_result_counts
                    .get(*c as usize)
                    .ok_or_else(|| format!("op {i}: call {c} has no result count"))?;
                let args = pop_n(g, &mut stack, &frames, argc as usize, i)?;
                if *c >= m.num_imported_funcs && analyzed.contains(c) {
                    for (k, a) in args.into_iter().enumerate() {
                        let p = g.local(*c, k as u32);
                        g.flow(a, p);
                    }
                    for r in 0..resc {
                        let n = g.ret(*c, r);
                        stack.push(n);
                    }
                } else {
                    // Host boundary (import or loud-skipped callee).
                    g.m0.host_exits.extend(args.iter().copied());
                    for r in 0..resc {
                        let n = g.fresh();
                        g.m0.opaque.insert(n);
                        g.host_entries.push((
                            format!("result {r} of the host call at function {fi} op {i}"),
                            n,
                        ));
                        stack.push(n);
                    }
                }
            }
            CallIndirect { type_index, .. } => {
                let ti = pop(g, &mut stack, &frames, i)?; // table index (a scalar)
                g.observe(ti);
                let argc = *m
                    .type_arg_counts
                    .get(*type_index as usize)
                    .ok_or_else(|| format!("op {i}: call_indirect type {type_index} unknown"))?;
                let resc = *m
                    .type_result_counts
                    .get(*type_index as usize)
                    .ok_or_else(|| format!("op {i}: call_indirect type {type_index} unknown"))?;
                let args = pop_n(g, &mut stack, &frames, argc as usize, i)?;
                let results: Vec<Node> = (0..resc).map(|_| g.fresh()).collect();
                let mut targets: Vec<u32> = m
                    .elem_func_indices
                    .iter()
                    .copied()
                    .filter(|t| {
                        *t >= m.num_imported_funcs
                            && analyzed.contains(t)
                            && m.func_arg_counts.get(*t as usize) == Some(&argc)
                            && m.func_result_counts.get(*t as usize) == Some(&resc)
                    })
                    .collect();
                targets.sort_unstable();
                targets.dedup();
                for t in targets {
                    for (k, &a) in args.iter().enumerate() {
                        let p = g.local(t, k as u32);
                        g.flow(a, p);
                    }
                    for (r, &res) in results.iter().enumerate() {
                        let n = g.ret(t, r as u32);
                        g.flow(n, res);
                    }
                }
                stack.extend(results);
            }
            LocalGet(l) => {
                let n = g.local(fi, *l);
                stack.push(n);
            }
            LocalSet(l) => {
                let v = pop(g, &mut stack, &frames, i)?;
                let n = g.local(fi, *l);
                g.flow(v, n);
            }
            LocalTee(l) => {
                let v = pop(g, &mut stack, &frames, i)?;
                let n = g.local(fi, *l);
                g.flow(v, n);
                stack.push(n);
            }
            GlobalGet(x) => {
                let n = g.global(*x);
                stack.push(n);
            }
            GlobalSet(x) => {
                let v = pop(g, &mut stack, &frames, i)?;
                let n = g.global(*x);
                g.flow(v, n);
            }
            Drop => {
                pop(g, &mut stack, &frames, i)?;
            }
            Select => {
                let c = pop(g, &mut stack, &frames, i)?;
                g.observe(c);
                let b = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                let r = g.fresh();
                g.flow(a, r);
                g.flow(b, r);
                stack.push(r);
            }
            I32Const(c) => {
                let n = g.fresh();
                g.consts.insert((fi, i), (*c, n));
                stack.push(n);
            }
            I32Load { .. }
            | I32Load8S { .. }
            | I32Load8U { .. }
            | I32Load16S { .. }
            | I32Load16U { .. }
            | I64Load { .. }
            | I64Load8S { .. }
            | I64Load8U { .. }
            | I64Load16S { .. }
            | I64Load16U { .. }
            | I64Load32S { .. }
            | I64Load32U { .. }
            | F32Load { .. }
            | F64Load { .. }
            | V128Load { .. } => {
                let a = pop(g, &mut stack, &frames, i)?;
                g.address(a, memory)?;
                let content = g.mem(memory);
                let r = g.fresh();
                g.flow(content, r);
                if memory == 0 {
                    g.m0.opaque.insert(r);
                    g.m0.load_results.insert(r, content);
                    g.m0.accesses.push(M0Access {
                        func: fi,
                        op: i,
                        addr: a,
                        offset: memarg_offset(inner).unwrap_or(0),
                        width: crate::proven_safe::access_width(inner),
                        len: None,
                        what: "a load",
                        is_copy_src: false,
                        result: Some(r),
                    });
                }
                stack.push(r);
            }
            I32Store { .. }
            | I32Store8 { .. }
            | I32Store16 { .. }
            | I64Store { .. }
            | I64Store8 { .. }
            | I64Store16 { .. }
            | I64Store32 { .. }
            | F32Store { .. }
            | F64Store { .. }
            | V128Store { .. } => {
                let v = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                g.address(a, memory)?;
                let content = g.mem(memory);
                g.flow(v, content);
                if memory == 0 {
                    g.m0.stores.push((a, v));
                    g.m0.accesses.push(M0Access {
                        func: fi,
                        op: i,
                        addr: a,
                        offset: memarg_offset(inner).unwrap_or(0),
                        width: crate::proven_safe::access_width(inner),
                        len: None,
                        what: "a store",
                        is_copy_src: false,
                        result: None,
                    });
                }
            }
            MemoryCopyBetween { dst_mem, src_mem } => {
                // #1145: a cross-/non-default-memory copy. Each address is
                // charged to its own memory, and the copied BYTES flow from
                // the source memory's contents into the destination's — so
                // a pointer carried across memories is still tracked (and,
                // field-insensitively, the two memories' contents join).
                let len = pop(g, &mut stack, &frames, i)?; // len
                let src = pop(g, &mut stack, &frames, i)?;
                let dst = pop(g, &mut stack, &frames, i)?;
                g.address(dst, *dst_mem)?;
                g.address(src, *src_mem)?;
                for (side, mem, is_src) in [(dst, *dst_mem, false), (src, *src_mem, true)] {
                    if mem == 0 {
                        g.m0.accesses.push(M0Access {
                            func: fi,
                            op: i,
                            addr: side,
                            offset: 0,
                            width: None,
                            len: Some(len),
                            what: "memory.copy (memory-0 side)",
                            is_copy_src: is_src,
                            result: None,
                        });
                    }
                }
                if *dst_mem == 0 && *src_mem == 0 {
                    g.m0.copies.push((dst, src));
                }
                if *src_mem == *dst_mem || !m.cross_copies_carry_no_pointers {
                    let from = g.mem(*src_mem);
                    let to = g.mem(*dst_mem);
                    g.flow(from, to);
                    g.joined_by_cross_copy |= *src_mem != *dst_mem;
                }
            }
            MemoryFill if memory != 0 => {
                pop(g, &mut stack, &frames, i)?; // len
                let val = pop(g, &mut stack, &frames, i)?;
                let dst = pop(g, &mut stack, &frames, i)?;
                g.address(dst, memory)?;
                let content = g.mem(memory);
                g.flow(val, content);
            }
            MemoryCopy | MemoryFill if memory == 0 => {
                // The decoder emits the bare variants for memory 0 only (a
                // cross- or non-default-memory form is decode-unsupported).
                let len = pop(g, &mut stack, &frames, i)?; // len
                let src_or_val = pop(g, &mut stack, &frames, i)?;
                let dst = pop(g, &mut stack, &frames, i)?;
                g.address(dst, 0)?;
                let content = g.mem(0);
                let copy = matches!(inner, MemoryCopy);
                g.m0.accesses.push(M0Access {
                    func: fi,
                    op: i,
                    addr: dst,
                    offset: 0,
                    width: None,
                    len: Some(len),
                    what: if copy {
                        "memory.copy (destination)"
                    } else {
                        "memory.fill (destination)"
                    },
                    is_copy_src: false,
                    result: None,
                });
                if copy {
                    g.address(src_or_val, 0)?;
                    g.m0.accesses.push(M0Access {
                        func: fi,
                        op: i,
                        addr: src_or_val,
                        offset: 0,
                        width: None,
                        len: Some(len),
                        what: "memory.copy (source)",
                        is_copy_src: true,
                        result: None,
                    });
                    g.m0.copies.push((dst, src_or_val));
                } else {
                    g.flow(src_or_val, content);
                    g.m0.stores.push((dst, src_or_val));
                }
            }
            MemorySize(_) => {
                let n = g.fresh();
                g.m0.opaque.insert(n);
                stack.push(n);
            }
            MemoryGrow(_) => {
                let a = pop(g, &mut stack, &frames, i)?;
                g.observe(a);
                let n = g.fresh();
                g.m0.opaque.insert(n);
                stack.push(n);
            }
            I32Eq | I32Ne | I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS
            | I32GeU | I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU
            | I64GeS | I64GeU => {
                let b = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                g.couple(a, b);
                g.observe(a);
                g.observe(b);
                let n = g.fresh();
                g.m0.opaque.insert(n);
                stack.push(n);
            }
            I32Sub | I64Sub => {
                let b = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                g.couple(a, b);
                let r = g.fresh();
                g.flow(a, r);
                g.flow(b, r);
                if matches!(inner, I32Sub) {
                    g.m0.binops.push((r, a, b, true));
                } else {
                    g.m0.opaque.insert(r);
                }
                stack.push(r);
            }
            other if memory == 0 => {
                let Some((pops, pushes)) = fixed_stack_effect(other) else {
                    return Err(format!(
                        "op {i}: {other:?} is not modeled by the provenance pass"
                    ));
                };
                let ins = pop_n(g, &mut stack, &frames, pops as usize, i)?;
                let add = matches!(other, I32Add) && ins.len() == 2;
                if !add {
                    // Consumed as a scalar (an operand of arithmetic other
                    // than add/sub, a conversion, `eqz` …).
                    for &v in &ins {
                        g.observe(v);
                    }
                }
                for _ in 0..pushes {
                    let r = g.fresh();
                    for &v in &ins {
                        g.flow(v, r);
                    }
                    if add {
                        g.m0.binops.push((r, ins[0], ins[1], false));
                    } else {
                        g.m0.opaque.insert(r);
                    }
                    stack.push(r);
                }
            }
            other => {
                return Err(format!(
                    "op {i}: {other:?} on memory {memory} is not modeled by the provenance pass"
                ));
            }
        }
    }
    if !frames.is_empty() {
        // An op stream without the trailing function `end`: close the body.
        let n = fn_results.len().min(stack.len());
        let base = stack.len() - n;
        for k in 0..n {
            g.flow(stack[base + k], fn_results[fn_results.len() - n + k]);
        }
    }
    Ok(())
}

/// A module global as the stack-pointer pick sees it.
pub struct NpaGlobal {
    pub index: u32,
    pub mutable: bool,
    /// `Some(v)` for an `i32.const v` initializer.
    pub init_i32: Option<i32>,
}

/// The per-memory layering decision for one module.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct NpaMultiMemoryPlan {
    /// The memory-0 stack-pointer global, picked among candidates that never
    /// reach a memory-k address (`None` ⇒ no stack-pointer rewrite).
    pub stack_pointer_global: Option<(u32, i32)>,
    /// Stack-pointer candidates excluded because they reach memory k — the
    /// other domains' stack pointers (`(index, init, memories)`).
    pub excluded_stack_pointers: Vec<(u32, i32, Vec<u32>)>,
    /// Per function index: op indices of the `i32.const`s in memory 0's
    /// static window that are memory-k OFFSETS and so stay raw.
    pub raw_consts: HashMap<u32, Vec<usize>>,
}

/// Decide the layering, or refuse. `memory0_bytes` is memory 0's static
/// extent (the classification window's upper bound).
pub fn plan(
    prov: &Provenance,
    globals: &[NpaGlobal],
    memory0_bytes: u32,
) -> Result<NpaMultiMemoryPlan, String> {
    let mut out = NpaMultiMemoryPlan::default();
    // A host-supplied value used in memory 0 AND memory k: the host would
    // have to pass a native pointer and a wasm offset at once.
    for (what, reach) in prov.host_entries() {
        let k = reach.memories_k();
        if reach.memory0() && !k.is_empty() {
            return Err(format!(
                "{what} may be used as an address in memory 0 AND in memory {k:?} — \
                 under --native-pointer-abi the host passes a memory-0 pointer \
                 native and a memory-k pointer as a wasm offset, so no single \
                 representation of this value is correct for both"
            ));
        }
    }
    // The identify_stack_pointer_global rule (mutable, i32 init in
    // (0, memory-0 bytes], largest init wins), restricted to globals whose
    // value never reaches a memory-k address.
    let mut candidates: Vec<(u32, i32)> = Vec::new();
    for gl in globals.iter().filter(|g| g.mutable) {
        let Some(v) = gl.init_i32 else { continue };
        if v <= 0 || (v as u32) > memory0_bytes {
            continue;
        }
        let reach = prov.global(gl.index);
        let k = reach.memories_k();
        if k.is_empty() {
            candidates.push((gl.index, v));
        } else if reach.memory0() {
            // A stack-pointer-shaped global used in memory 0 AND memory k:
            // rebasing it breaks memory k, not rebasing it breaks memory 0.
            return Err(format!(
                "global {} (a mutable i32 with init 0x{v:x}, the stack-pointer \
                 shape) may be used as an address in memory 0 AND in memory {k:?} \
                 — under --native-pointer-abi memory 0's stack pointer is rebased \
                 to a native pointer while memory k stays a wasm offset, so no \
                 single representation of it is correct for both",
                gl.index
            ));
        } else {
            out.excluded_stack_pointers.push((gl.index, v, k));
        }
    }
    out.stack_pointer_global = candidates.into_iter().max_by_key(|&(_, v)| v);
    let Some((sp_idx, sp_init)) = out.stack_pointer_global else {
        // No stack-pointer rewrite: rule (1) never fires, and the #1568
        // local plan relocates only locals read exclusively as MEMORY-0
        // address operands, so nothing memory-k can be rewritten.
        return Ok(out);
    };
    let window = sp_init as u32..memory0_bytes;
    for (f, i, c, reach) in prov.consts() {
        if !window.contains(&(c as u32)) {
            continue;
        }
        let k = reach.memories_k();
        if k.is_empty() {
            continue;
        }
        if reach.memory0() {
            return Err(format!(
                "function {f} op {i}: the constant 0x{c:x} is inside memory 0's \
                 static window [0x{:x}, 0x{memory0_bytes:x}) (stack-pointer global \
                 {sp_idx}) and may be used as an address in memory 0 AND in memory \
                 {k:?} — under --native-pointer-abi memory 0 is native \
                 (`__synth_wasm_data + C`) while memory k stays a wasm offset \
                 (`__synth_wasm_data_<k> + C`), so no single representation of \
                 this value is correct for both",
                window.start
            ));
        }
        out.raw_consts.entry(f).or_default().push(i);
    }
    Ok(out)
}

// ===========================================================================
// RQ-91-NPAMODEL: the memory-0 native-pointer decision.
// ===========================================================================

/// The memarg `offset` of a scalar memory access (`None` for an op without
/// one). Shared by the provenance walk and the selector's #1580 fold.
pub fn memarg_offset(op: &WasmOp) -> Option<u32> {
    use WasmOp::*;
    match op {
        I32Load { offset, .. }
        | I32Load8S { offset, .. }
        | I32Load8U { offset, .. }
        | I32Load16S { offset, .. }
        | I32Load16U { offset, .. }
        | I32Store { offset, .. }
        | I32Store8 { offset, .. }
        | I32Store16 { offset, .. }
        | I64Load { offset, .. }
        | I64Load8S { offset, .. }
        | I64Load8U { offset, .. }
        | I64Load16S { offset, .. }
        | I64Load16U { offset, .. }
        | I64Load32S { offset, .. }
        | I64Load32U { offset, .. }
        | I64Store { offset, .. }
        | I64Store8 { offset, .. }
        | I64Store16 { offset, .. }
        | I64Store32 { offset, .. }
        | F32Load { offset, .. }
        | F64Load { offset, .. }
        | F32Store { offset, .. }
        | F64Store { offset, .. }
        | V128Load { offset, .. }
        | V128Store { offset, .. } => Some(*offset),
        _ => None,
    }
}

/// The memarg `offset` of a scalar memory access, mutably.
pub fn memarg_offset_mut(op: &mut WasmOp) -> Option<&mut u32> {
    use WasmOp::*;
    match op {
        I32Load { offset, .. }
        | I32Load8S { offset, .. }
        | I32Load8U { offset, .. }
        | I32Load16S { offset, .. }
        | I32Load16U { offset, .. }
        | I32Store { offset, .. }
        | I32Store8 { offset, .. }
        | I32Store16 { offset, .. }
        | I64Load { offset, .. }
        | I64Load8S { offset, .. }
        | I64Load8U { offset, .. }
        | I64Load16S { offset, .. }
        | I64Load16U { offset, .. }
        | I64Load32S { offset, .. }
        | I64Load32U { offset, .. }
        | I64Store { offset, .. }
        | I64Store8 { offset, .. }
        | I64Store16 { offset, .. }
        | I64Store32 { offset, .. }
        | F32Load { offset, .. }
        | F64Load { offset, .. }
        | F32Store { offset, .. }
        | F64Store { offset, .. }
        | V128Load { offset, .. }
        | V128Store { offset, .. } => Some(offset),
        _ => None,
    }
}

/// The op that pushed the value at operand distance `back` (1 = the operand
/// pushed last) of the op at `idx`, found by walking backwards over
/// STRAIGHT-LINE ops with exact stack effects. `None` when the walk meets a
/// control-region op, a call, or anything unmodeled, or when the value comes
/// from an op that pushes more than one value.
pub fn operand_producer(wasm_ops: &[WasmOp], idx: usize, back: u32) -> Option<usize> {
    let mut d = back;
    let mut j = idx;
    while j > 0 {
        j -= 1;
        let (pops, pushes) = crate::wasm_stack_check::straight_line_stack_effect(&wasm_ops[j])?;
        if d <= pushes {
            return (pushes == 1).then_some(j);
        }
        d = d - pushes + pops;
    }
    None
}

/// #1580 / RQ-91-NPAMODEL: the `--native-pointer-abi` EFFECTIVE-ADDRESS
/// FOLDS of one function — `(const op j, access op idx, C + O)` for every
/// `i32.const C … access offset=O` (O != 0, scalar, not v128) whose constant
/// is found by an exact backward walk over straight-line ops, and where the
/// relocation must carry the effective address: with a stack-pointer global,
/// when one part is relocated by the selector's #237 / #739 rules and `C + O`
/// is itself in that window; in any module, when `j` is a constant the
/// memory-0 decision relocates (`reloc`). `i32.const (C+O) … offset=0` is
/// exact wasm (the constant's only consumer is this access), and the mixed
/// split then retargets the relocation by the region of the ACCESSED byte.
/// The selector applies these; the memory-0 decision reads them. One source.
pub fn npa_offset_folds(
    wasm_ops: &[WasmOp],
    sp_init: Option<i32>,
    memory0_bytes: u32,
    reloc: &std::collections::HashSet<usize>,
) -> Vec<(usize, usize, u32)> {
    let base = sp_init.filter(|&v| v > 0).map(|v| v as u32);
    let in_window = |a: u32| base.is_some_and(|b| b <= a && a < memory0_bytes);
    let mut out = Vec::new();
    for (idx, op) in wasm_ops.iter().enumerate() {
        let Some(offset) = memarg_offset(op) else {
            continue;
        };
        if offset == 0 || matches!(op, WasmOp::V128Load { .. } | WasmOp::V128Store { .. }) {
            continue;
        }
        let back = if crate::proven_safe::access_width(op).is_some()
            && matches!(
                op,
                WasmOp::I32Store { .. }
                    | WasmOp::I32Store8 { .. }
                    | WasmOp::I32Store16 { .. }
                    | WasmOp::I64Store { .. }
                    | WasmOp::I64Store8 { .. }
                    | WasmOp::I64Store16 { .. }
                    | WasmOp::I64Store32 { .. }
                    | WasmOp::F32Store { .. }
                    | WasmOp::F64Store { .. }
            ) {
            2
        } else {
            1
        };
        let Some(j) = operand_producer(wasm_ops, idx, back) else {
            continue;
        };
        let WasmOp::I32Const(c) = wasm_ops[j] else {
            continue;
        };
        let Some(eff) = (c as u32).checked_add(offset) else {
            continue;
        };
        let by_sp = base
            .is_some_and(|b| (in_window(c as u32) || (c != 0 && offset >= b)) && in_window(eff));
        if by_sp || reloc.contains(&j) {
            out.push((j, idx, eff));
        }
    }
    out
}

/// The ELF builder's `--native-pointer-abi` MIXED SPLIT gate (#354), stated
/// once: memory 0's statics are laid out NON-contiguously — the zero
/// reservation as a `.bss` under `__synth_wasm_data`, each data segment packed
/// 4-aligned into `.data` under its own `__synth_wasm_seg_K` — exactly when
/// there is a data segment and every segment sits at or above the
/// stack-pointer init (0 without one). Otherwise one contiguous image ships.
/// (The builder additionally needs every static reloc in the retargetable
/// `Abs32` form, which every shipped selector path emits.)
pub fn npa_split_layout(segment_offsets: &[u32], sp_init: Option<i32>) -> bool {
    let base = sp_init.map_or(0, |v| v.max(0) as u32);
    !segment_offsets.is_empty() && segment_offsets.iter().all(|&o| o >= base)
}

/// The inputs of [`Provenance::memory0_plan`].
pub struct Memory0Inputs<'a> {
    /// Function names for the diagnostics (export name or `func_N`).
    pub func_names: &'a HashMap<u32, String>,
    /// Memory 0's static extent in bytes as the SELECTOR sees it (its
    /// `linear_memory_bytes`, the end of the #237 window).
    pub memory0_bytes: u32,
    /// Memory 0's declared minimum in bytes (an imported memory 0 included).
    pub memory0_declared_bytes: u32,
    /// The memory-0 stack-pointer global the compile uses, `(index, init)`,
    /// only when its init is positive.
    pub stack_pointer: Option<(u32, i32)>,
    /// Memory 0's active data segments `(offset, bytes)`, in declaration
    /// order (empty ones included; they own no byte).
    pub data_segments: &'a [(u32, Vec<u8>)],
    /// `--safety-bounds software|mask`.
    pub guarded_bounds: bool,
    /// Every analysed function's op stream (for the #1580 fold).
    pub func_ops: &'a HashMap<u32, &'a [WasmOp]>,
}

/// The decision, per function.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Memory0Plan {
    /// Op indices of the `i32.const`s to emit as `__synth_wasm_data + C`
    /// BELOW the stack-pointer window — the window `[sp_init, memory-0
    /// bytes)` keeps the selector's own #237 rule (every constant there is
    /// relocated), so it is never listed here.
    pub reloc_consts: HashMap<u32, Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Vals {
    Known(std::collections::BTreeSet<u32>),
    Top,
}

const VALS_CAP: usize = 64;
const SITES_CAP: usize = 64;

// A value's dynamic origins.
const DYN_HOST: u8 = 1;
const DYN_SP: u8 = 2;
const DYN_GLOBAL: u8 = 4;
const DYN_LOAD: u8 = 8;
const DYN_OPAQUE: u8 = 16;

// Region bits: 0..=61 data segment k, 62 NATIVE (memory no static names:
// the shadow stack, a host buffer), 63 the zero reservation / a byte no
// segment owns.
const R_NATIVE: u64 = 1 << 62;
const R_RESERVATION: u64 = 1 << 63;

fn region_bit(k: Option<usize>) -> u64 {
    match k {
        Some(k) if k < 62 => 1 << k,
        Some(_) => R_RESERVATION | ((1u64 << 62) - 1), // > 62 segments: any
        None => R_RESERVATION,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Sum {
    vals: Vals,
    /// Candidate static constants (site ids) that reach this value through
    /// value flows and add/sub — never through memory or a global.
    sites: std::collections::BTreeSet<usize>,
    many_sites: bool,
    /// Constants in the selector's #237 window that reach it the same way
    /// (`spz_many` once more than `SITES_CAP` do).
    spz: std::collections::BTreeSet<u32>,
    spz_many: bool,
    dynamic: u8,
    /// Memory-0 regions the value may point into.
    regions: u64,
    /// May be a WORD read from a data segment that holds a wasm address:
    /// `(load function, load op, word address)`.
    data: Option<(u32, usize, u32)>,
}

impl Sum {
    fn bottom() -> Sum {
        Sum {
            vals: Vals::Known(Default::default()),
            sites: Default::default(),
            many_sites: false,
            spz: Default::default(),
            spz_many: false,
            dynamic: 0,
            regions: 0,
            data: None,
        }
    }
    fn join(&mut self, o: &Sum, keep_values: bool) {
        self.dynamic |= o.dynamic;
        self.regions |= o.regions;
        if self.data.is_none() {
            self.data = o.data;
        }
        if keep_values {
            self.many_sites |= o.many_sites;
            self.spz_many |= o.spz_many;
            self.spz.extend(o.spz.iter().copied());
            self.sites.extend(o.sites.iter().copied());
            if let (Vals::Known(a), Vals::Known(b)) = (&mut self.vals, &o.vals) {
                a.extend(b.iter().copied());
            } else {
                self.vals = Vals::Top;
            }
        }
    }
}

/// One `i32.const` (or implicit zero) the decision may relocate.
struct Site {
    func: u32,
    /// `None` for a local's implicit zero.
    op: Option<usize>,
    value: u32,
    node: Node,
}

impl Provenance {
    /// RQ-91-NPAMODEL (#739, #1568, #1604, #1672, #1661): memory 0's address
    /// provenance under `--native-pointer-abi`, decided ONCE for the module.
    ///
    /// Under the ABI R11 is 0, so a memory-0 access dereferences its address
    /// as a NATIVE pointer. A wasm static at offset `C` lives at
    /// `__synth_wasm_data + C`, so a value that is a wasm static address must
    /// have been rewritten to that native form before it is dereferenced.
    /// This pass classifies every value the accesses see and either names
    /// the constants to rewrite or refuses the module, loudly, with a named
    /// diagnostic. The rules are the ABI (docs/embedder-abi-relocatable-arm.md):
    ///
    /// * WITH a stack-pointer global, a constant in `[sp_init, memory-0
    ///   bytes)` is a pointer, relocated by the selector wherever it appears
    ///   (the #237 rule, unchanged), and a run-time value added to it is an
    ///   index. Statics BELOW `sp_init` (data placed under the stack) are
    ///   decided here like a stackless module's.
    /// * An address computed only from constants (through locals, select,
    ///   add/sub) is a static: its pointer term — the larger term of an add,
    ///   the minuend of a sub — is relocated at its definition, provided no
    ///   comparison, branch or non-add arithmetic consumes it as a scalar.
    /// * With a memory-0 data segment and no stack-pointer global, a constant
    ///   in the static region `[lowest segment, memory-0 bytes)` — or a
    ///   memarg offset touching it — beside a run-time value is ambiguous
    ///   (a static base plus an index, or a native pointer plus an offset)
    ///   and refused: `npa-dynamic-static-offset` (#1568 shape 2). Without a
    ///   data segment there is no static region: a run-time value is native
    ///   and a constant added to it an offset (`MMIO_BASE + reg`).
    /// * A data-segment word holding a value in the static region is a WASM
    ///   address the image does not relocate. A full word that may have been
    ///   loaded from one and is then dereferenced as the POINTER (not as an
    ///   index added to a static) is refused: `npa-data-pointer` (#1672).
    ///   Memory is modelled per region (each data segment, the reservation,
    ///   and native memory such as the stack), so a copy of such a word is
    ///   followed. A host-supplied pointer into the statics is one the module
    ///   produced earlier (a realloc result, an exported address): it may
    ///   point into every region whose address left the module.
    /// * A constant effective address whose bytes span two regions of the
    ///   split layout, or whose relocated constant names another region, is
    ///   refused — `npa-region-straddle` (#1604) — as is a bulk op with a
    ///   constant destination and a run-time length there.
    /// * `--safety-bounds software|mask` guard a wasm OFFSET against R10; a
    ///   memory-0 address here is native, so a module with any memory-0
    ///   access is refused: `npa-software-bounds` (#1661).
    pub fn memory0_plan(&self, inp: &Memory0Inputs) -> Result<Memory0Plan, String> {
        let g = &self.graph;
        let f = &g.m0;
        let n = g.preds.len();
        let name = |func: u32| {
            inp.func_names
                .get(&func)
                .cloned()
                .unwrap_or_else(|| format!("func_{func}"))
        };
        // ---- #1661 --------------------------------------------------------
        if inp.guarded_bounds
            && let Some(a) = f.accesses.first()
        {
            return Err(format!(
                "npa-software-bounds (#1661): --native-pointer-abi with --safety-bounds \
                 software|mask is refused for this module — function '{}' (wasm function \
                 index {}) has {} on memory 0 at op {}. Under the native-pointer ABI a \
                 memory-0 address is a NATIVE pointer (R11 = 0), and the software and mask \
                 guards compare a wasm OFFSET against R10 (memory 0's size), so in-bounds \
                 accesses would trap or be masked to the wrong address. Memory-k accesses \
                 keep their own guard; a module that touches only memory k is accepted. No \
                 object is written. Drop --safety-bounds, use --safety-bounds mpu \
                 --embedder-mpu, or drop --native-pointer-abi.",
                name(a.func),
                a.func,
                a.what,
                a.op
            ));
        }
        // ---- the regions --------------------------------------------------
        let segs: Vec<(usize, u32, &Vec<u8>)> = inp
            .data_segments
            .iter()
            .enumerate()
            .filter(|(_, (_, b))| !b.is_empty())
            .map(|(k, (o, b))| (k, *o, b))
            .collect();
        let region_of = |a: u64| -> Option<usize> {
            segs.iter()
                .rev()
                .find(|&&(_, o, b)| a >= u64::from(o) && a - u64::from(o) < b.len() as u64)
                .map(|&(k, _, _)| k)
        };
        let lowest = segs.iter().map(|&(_, o, _)| o).min();
        let data_end: u64 = segs
            .iter()
            .map(|&(_, o, b)| u64::from(o) + b.len() as u64)
            .max()
            .unwrap_or(0);
        let mem_end: u64 = u64::from(inp.memory0_bytes)
            .max(u64::from(inp.memory0_declared_bytes))
            .max(data_end);
        let sp_init = inp.stack_pointer.map(|(_, v)| v as u32);
        let split = npa_split_layout(
            &segs.iter().map(|&(_, o, _)| o).collect::<Vec<_>>(),
            inp.stack_pointer.map(|(_, v)| v),
        );
        let in_spz =
            |v: u32| sp_init.is_some_and(|s| v >= s && u64::from(v) < u64::from(inp.memory0_bytes));
        // A constant that may be a static in a constant-only address.
        let pure_lo: u32 = match sp_init {
            Some(s) => lowest.map_or(s, |l| l.min(s)),
            None => 0,
        };
        let candidate = |v: u32| v >= pure_lo && u64::from(v) < mem_end && !in_spz(v);
        // The static region a constant beside a RUN-TIME value is judged in.
        let (zlo, zhi): (u64, u64) = match (lowest, sp_init) {
            (Some(l), Some(s)) => (u64::from(l), u64::from(s).max(u64::from(l))),
            (Some(l), None) => (u64::from(l), mem_end),
            (None, _) => (0, 0),
        };
        let in_zone = |lo: u64, len: u64| zlo < zhi && lo < zhi && lo + len.max(1) > zlo;
        // ---- data words that hold a wasm address (#1672) ------------------
        let mut ptr_words: Vec<(u32, usize)> = Vec::new();
        let mut ptr_regions: u64 = 0;
        if let Some(lo) = lowest {
            let span = (data_end - u64::from(lo)) as usize;
            let mut img = vec![0u8; span];
            let mut cov = vec![false; span];
            for &(_, o, b) in &segs {
                let s = (o - lo) as usize;
                img[s..s + b.len()].copy_from_slice(b);
                cov[s..s + b.len()].iter_mut().for_each(|c| *c = true);
            }
            let ptr_lo = sp_init.map_or(lo, |s| s.min(lo));
            let mut a = u64::from(lo.next_multiple_of(4));
            while a + 4 <= data_end {
                let s = (a - u64::from(lo)) as usize;
                if cov[s..s + 4].iter().all(|&c| c) {
                    let w = u32::from_le_bytes([img[s], img[s + 1], img[s + 2], img[s + 3]]);
                    if w != 0 && w >= ptr_lo && u64::from(w) < mem_end {
                        let k = region_of(a).unwrap_or(usize::MAX);
                        ptr_words.push((a as u32, k));
                        ptr_regions |= region_bit(Some(k));
                    }
                }
                a += 4;
            }
        }
        // The first pointer word an access of `w` bytes at `ea` reads.
        let word_in = |ea: u64, w: u64| -> Option<u32> {
            ptr_words
                .iter()
                .find(|&&(wa, _)| u64::from(wa) + 4 > ea && u64::from(wa) < ea + w.max(1))
                .map(|&(wa, _)| wa)
        };
        let word_of_regions = |r: u64| -> Option<u32> {
            ptr_words
                .iter()
                .find(|&&(_, k)| region_bit(Some(k)) & r != 0)
                .map(|&(wa, _)| wa)
        };
        // ---- sites and seeds ----------------------------------------------
        let mut sites: Vec<Site> = Vec::new();
        let mut site_of: HashMap<Node, usize> = HashMap::new();
        let mut consts_by_node: HashMap<Node, u32> = HashMap::new();
        let mut const_list: Vec<_> = g.consts.iter().collect();
        const_list.sort_by_key(|(k, _)| **k);
        for (&(func, op), &(c, node)) in const_list {
            consts_by_node.insert(node, c as u32);
            if candidate(c as u32) {
                site_of.insert(node, sites.len());
                sites.push(Site {
                    func,
                    op: Some(op),
                    value: c as u32,
                    node,
                });
            }
        }
        for &(func, _, node) in &f.zero_inits {
            consts_by_node.insert(node, 0);
            if candidate(0) {
                site_of.insert(node, sites.len());
                sites.push(Site {
                    func,
                    op: None,
                    value: 0,
                    node,
                });
            }
        }
        let host_nodes: std::collections::HashSet<Node> =
            g.host_entries.iter().map(|(_, nd)| *nd).collect();
        let global_nodes: HashMap<Node, u32> = g.globals.iter().map(|(&k, &v)| (v, k)).collect();
        let binop_of: HashMap<Node, (Node, Node, bool)> = f
            .binops
            .iter()
            .map(|&(r, a, b, s)| (r, (a, b, s)))
            .collect();
        let loads: HashMap<Node, &M0Access> = f
            .accesses
            .iter()
            .filter_map(|a| a.result.map(|r| (r, a)))
            .collect();
        let mut succ: Vec<Vec<Node>> = vec![Vec::new(); n];
        for v in 0..n {
            for &p in &f.fpreds[v] {
                succ[p].push(v);
            }
        }
        for (&r, a) in &loads {
            succ[a.addr].push(r);
        }
        // Where an address may point, as region bits.
        let points_to = |s: &Sum| -> u64 {
            let mut r = s.regions;
            if s.dynamic != 0 || r == 0 {
                r |= R_NATIVE;
            }
            if let Vals::Known(vs) = &s.vals
                && s.dynamic == 0
            {
                for &v in vs {
                    if lowest.is_some() && u64::from(v) < mem_end {
                        r |= region_bit(region_of(u64::from(v)));
                    }
                }
            }
            r
        };
        // ---- the fixpoint (nodes, then memory buckets, then escapes) ------
        let mut sum: Vec<Sum> = vec![Sum::bottom(); n];
        let mut bucket: Vec<Sum> = vec![Sum::bottom(); 64];
        let mut escaped: u64 = 0;
        let mut first = true;
        loop {
            let mut work: Vec<Node> = if first {
                (0..n).collect()
            } else {
                // Only the bucket readers and the host values can change.
                loads
                    .keys()
                    .copied()
                    .chain(host_nodes.iter().copied())
                    .collect()
            };
            first = false;
            let mut queued = vec![false; n];
            for &v in &work {
                queued[v] = true;
            }
            while let Some(v) = work.pop() {
                queued[v] = false;
                let mut s = Sum::bottom();
                let is_load = loads.contains_key(&v);
                let blocked = is_load || global_nodes.contains_key(&v);
                let opaque = f.opaque.contains(&v) && !binop_of.contains_key(&v);
                if !is_load {
                    for &p in &f.fpreds[v] {
                        s.join(&sum[p], !blocked);
                    }
                }
                if opaque {
                    // A scalar result: neither a static nor a data word.
                    s.sites.clear();
                    s.many_sites = false;
                    s.spz.clear();
                    s.spz_many = false;
                    s.data = None;
                    s.vals = Vals::Top;
                    s.dynamic |= DYN_OPAQUE;
                }
                if let Some(&c) = consts_by_node.get(&v) {
                    s.vals = Vals::Known([c].into_iter().collect());
                    if in_spz(c) {
                        s.spz.insert(c);
                    }
                    if lowest.is_some() && u64::from(c) < mem_end && c >= pure_lo {
                        s.regions |= region_bit(region_of(u64::from(c)));
                    }
                }
                if let Some(&k) = site_of.get(&v) {
                    s.sites.insert(k);
                }
                if let Some(&(a, b, is_sub)) = binop_of.get(&v) {
                    s.vals = match (&sum[a].vals, &sum[b].vals) {
                        (Vals::Known(x), Vals::Known(y)) if x.len() * y.len() <= VALS_CAP => {
                            Vals::Known(
                                x.iter()
                                    .flat_map(|&p| {
                                        y.iter().map(move |&q| {
                                            if is_sub {
                                                p.wrapping_sub(q)
                                            } else {
                                                p.wrapping_add(q)
                                            }
                                        })
                                    })
                                    .collect(),
                            )
                        }
                        _ => Vals::Top,
                    };
                }
                if host_nodes.contains(&v) {
                    s.vals = Vals::Top;
                    s.dynamic |= DYN_HOST;
                    s.regions |= escaped;
                }
                if let Some(&gi) = global_nodes.get(&v) {
                    s.vals = Vals::Top;
                    s.dynamic |= if inp.stack_pointer.is_some_and(|(i, _)| i == gi) {
                        DYN_SP
                    } else {
                        DYN_GLOBAL
                    };
                }
                if let Some(acc) = loads.get(&v) {
                    let a = &sum[acc.addr];
                    let pt = points_to(a);
                    for (k, b) in bucket.iter().enumerate() {
                        if pt & (1 << k) != 0 {
                            s.join(b, false);
                        }
                    }
                    s.vals = Vals::Top;
                    s.dynamic |= DYN_LOAD;
                    // A FULL WORD read from a segment holding a wasm address.
                    if s.data.is_none() && acc.width.is_some_and(|w| w >= 4) {
                        let w = u64::from(acc.width.unwrap_or(4));
                        let hit = match &a.vals {
                            Vals::Known(vs) if a.dynamic == 0 => vs
                                .iter()
                                .find_map(|&x| word_in(u64::from(x) + u64::from(acc.offset), w)),
                            _ if pt & ptr_regions != 0 => word_of_regions(pt & ptr_regions),
                            _ => None,
                        };
                        if let Some(wa) = hit {
                            s.data = Some((acc.func, acc.op, wa));
                        }
                    }
                }
                if let Vals::Known(k) = &s.vals
                    && k.len() > VALS_CAP
                {
                    s.vals = Vals::Top;
                }
                if s.sites.len() > SITES_CAP {
                    s.many_sites = true;
                }
                if s.spz.len() > SITES_CAP {
                    s.spz.clear();
                    s.spz_many = true;
                }
                if f.fpreds[v].is_empty()
                    && !consts_by_node.contains_key(&v)
                    && !binop_of.contains_key(&v)
                    && !is_load
                {
                    s.vals = Vals::Top;
                }
                if s != sum[v] {
                    sum[v] = s;
                    for &w in &succ[v] {
                        if !queued[w] {
                            queued[w] = true;
                            work.push(w);
                        }
                    }
                }
            }
            // Memory buckets: what each region may hold.
            let mut nb: Vec<Sum> = vec![Sum::bottom(); 64];
            for &(addr, val) in &f.stores {
                let pt = points_to(&sum[addr]);
                for (k, b) in nb.iter_mut().enumerate() {
                    if pt & (1 << k) != 0 {
                        b.join(&sum[val], false);
                    }
                }
            }
            for &(dst, src) in &f.copies {
                let (pd, ps) = (points_to(&sum[dst]), points_to(&sum[src]));
                let mut moved = Sum::bottom();
                for (k, b) in bucket.iter().enumerate() {
                    if ps & (1 << k) != 0 {
                        moved.join(b, false);
                    }
                }
                if moved.data.is_none()
                    && let Some(wa) = word_of_regions(ps & ptr_regions)
                {
                    let acc = f.accesses.iter().find(|a| a.addr == src && a.is_copy_src);
                    moved.data = Some((acc.map_or(0, |a| a.func), acc.map_or(0, |a| a.op), wa));
                }
                for (k, b) in nb.iter_mut().enumerate() {
                    if pd & (1 << k) != 0 {
                        b.join(&moved, false);
                    }
                }
            }
            // R3': host pointers into the statics are ones the module handed out.
            let mut esc = escaped;
            for &x in &f.host_exits {
                esc |= sum[x].regions;
            }
            let mut grew = esc != escaped;
            escaped = esc;
            for (k, b) in nb.into_iter().enumerate() {
                let mut j = bucket[k].clone();
                j.join(&b, false);
                if j != bucket[k] {
                    bucket[k] = j;
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        // ---- observed-as-scalar (backward over the directed flows) --------
        // A value that leaves the module (an export result, an import
        // argument) is observed too: the host sees its number. A static the
        // module hands out as a pointer is relocated by the #237 window; one
        // below it would change what the host receives.
        let mut obs = vec![false; n];
        let mut work: Vec<Node> = f
            .observed
            .iter()
            .chain(f.host_exits.iter())
            .copied()
            .collect();
        while let Some(v) = work.pop() {
            if obs[v] {
                continue;
            }
            obs[v] = true;
            work.extend(f.fpreds[v].iter().copied());
        }
        let region_name = |k: Option<usize>| match k {
            Some(k) => {
                let (o, b) = &inp.data_segments[k];
                format!(
                    "data segment {k} [0x{o:x}, 0x{:x})",
                    u64::from(*o) + b.len() as u64
                )
            }
            None => "the zero-initialised reservation".to_string(),
        };
        // ---- per-access decisions -----------------------------------------
        let mut offset_role: std::collections::HashSet<usize> = Default::default();
        let mut base_role: std::collections::HashSet<usize> = Default::default();
        let mut pure: Vec<&M0Access> = Vec::new();
        for acc in &f.accesses {
            let s = &sum[acc.addr];
            // An address anchored by a static constant: a loaded value in it
            // is an index, never the pointer.
            let anchored = !s.spz.is_empty() || s.spz_many || !s.sites.is_empty();
            if let Some((lf, lop, wa)) = s.data
                && !anchored
            {
                let k = region_of(u64::from(wa)).unwrap_or(0);
                let so = wa - inp.data_segments.get(k).map_or(0, |d| d.0);
                let word = word_at(inp.data_segments, wa).unwrap_or(0);
                return Err(format!(
                    "npa-data-pointer (#1672): --native-pointer-abi refused for the whole \
                     module — function '{}' (wasm function index {}) dereferences, in {} at \
                     op {}, a value that may be the word loaded by the load at op {lop} of \
                     function '{}' (wasm function index {lf}): data segment {k} holds the \
                     wasm address 0x{word:x} at segment offset 0x{so:x} (wasm address \
                     0x{wa:x}). Initialised data ships verbatim, so that word is a WASM \
                     address, while a memory-0 address under this ABI is NATIVE: the \
                     dereference would silently read absolute 0x{word:x}. No object is \
                     written; --allow-skipped-exports does not cover this. Build the \
                     pointer at run time (where it is relocated) instead of storing it in \
                     initialised data, or drop --native-pointer-abi.",
                    name(acc.func),
                    acc.func,
                    acc.what,
                    acc.op,
                    name(lf),
                ));
            }
            if s.dynamic != 0 {
                let w = u64::from(acc.width.unwrap_or(1));
                let zoned = s
                    .sites
                    .iter()
                    .map(|&k| sites[k].value)
                    .find(|&v| in_zone(u64::from(v), 1));
                let off_in = acc.offset != 0 && in_zone(u64::from(acc.offset), w);
                let sp_only = sp_init.is_some() && s.dynamic == DYN_SP;
                if (zoned.is_some() || off_in || (s.many_sites && zhi > zlo)) && !sp_only {
                    let what = match zoned {
                        Some(v) => format!("the constant 0x{v:x}"),
                        None => format!("the memarg offset 0x{:x}", acc.offset),
                    };
                    return Err(format!(
                        "npa-dynamic-static-offset (#1568): --native-pointer-abi refused for \
                         the whole module — function '{}' (wasm function index {}): {} at op \
                         {} with memarg offset 0x{:x} adds {what}, which lies in the module's \
                         static region [0x{zlo:x}, 0x{zhi:x}), to a value computed at run \
                         time. synth cannot tell a static base plus an index from a native \
                         pointer plus an offset there, and the wrong choice silently reads or \
                         writes the wrong address. No object is written; \
                         --allow-skipped-exports does not cover this. Give the module a \
                         stack-pointer global (the toolchain `__stack_pointer`) placed below \
                         its data, keep run-time memarg offsets below 0x{zlo:x}, or drop \
                         --native-pointer-abi.",
                        name(acc.func),
                        acc.func,
                        acc.what,
                        acc.op,
                        acc.offset,
                    ));
                }
                offset_role.extend(s.sites.iter().copied());
            } else {
                base_role.extend(s.sites.iter().copied());
                pure.push(acc);
            }
        }
        // add / sub roles in constant-only address arithmetic.
        for &(r, a, b, is_sub) in &f.binops {
            if g.taint[r] & 1 == 0 || sum[r].dynamic != 0 {
                continue;
            }
            let (sa, sb) = (&sum[a], &sum[b]);
            if is_sub {
                offset_role.extend(sb.sites.iter().copied());
                continue;
            }
            let anch = |s: &Sum| !s.spz.is_empty() || s.spz_many || !s.sites.is_empty();
            if !anch(sa) || !anch(sb) {
                continue;
            }
            let max = |s: &Sum| match &s.vals {
                Vals::Known(v) => v.iter().max().copied(),
                Vals::Top => None,
            };
            match (max(sa), max(sb)) {
                (Some(x), Some(y)) if x >= y => offset_role.extend(sb.sites.iter().copied()),
                (Some(_), Some(_)) => offset_role.extend(sa.sites.iter().copied()),
                _ => offset_role.extend(sa.sites.iter().chain(sb.sites.iter()).copied()),
            }
        }
        // The relocated constants.
        let mut plan = Memory0Plan::default();
        let mut relocated: std::collections::HashSet<usize> = Default::default();
        for (k, site) in sites.iter().enumerate() {
            if !base_role.contains(&k) || offset_role.contains(&k) {
                continue;
            }
            let Some(op) = site.op else {
                return Err(format!(
                    "npa-static-unrelocatable (#1568): --native-pointer-abi refused for the \
                     whole module — in function '{}' (wasm function index {}) a local's \
                     implicit zero initial value may be read and dereferenced as the static \
                     address 0x0; an implicit value has no definition to relocate. No object \
                     is written. Set the local before every read, or drop \
                     --native-pointer-abi.",
                    name(site.func),
                    site.func
                ));
            };
            if obs[site.node] {
                return Err(format!(
                    "npa-static-observed (#1568): --native-pointer-abi refused for the whole \
                     module — in function '{}' (wasm function index {}) the constant 0x{:x} \
                     at op {op} is dereferenced as a memory-0 static address AND consumed as \
                     a scalar (a comparison, a branch condition, or arithmetic other than \
                     add/sub). Relocating it would change what the scalar use sees; not \
                     relocating it would dereference the wrong address. No object is \
                     written. Keep the static address and the scalar in separate values, or \
                     drop --native-pointer-abi.",
                    name(site.func),
                    site.func,
                    site.value
                ));
            }
            relocated.insert(k);
            plan.reloc_consts.entry(site.func).or_default().push(op);
        }
        // Positional fallback: a constant-only address whose static effective
        // address none of its constants carries (each is below the static
        // range, e.g. `i32.const 0x1800 … offset=0x1000` under a stack
        // pointer at 0x2000), but whose address operand IS one `i32.const`
        // consumed only by this access. That constant is relocated, and the
        // #1580 fold below makes its relocation carry the effective address.
        let node_op: HashMap<Node, (u32, usize)> = g
            .consts
            .iter()
            .map(|(&(fi, o), &(_, nd))| (nd, (fi, o)))
            .collect();
        let mut fallback: HashMap<(u32, usize), u32> = HashMap::new();
        for acc in &pure {
            let s = &sum[acc.addr];
            let Some(&(fi, op)) = node_op.get(&acc.addr) else {
                continue;
            };
            let c = consts_by_node[&acc.addr];
            let Some(ea) = c.checked_add(acc.offset) else {
                continue;
            };
            let carried = !s.spz.is_empty()
                || s.spz_many
                || s.sites.iter().any(|k| relocated.contains(k))
                || sp_init.is_some_and(|sp| acc.offset != 0 && acc.offset >= sp);
            if ea >= pure_lo && u64::from(ea) < mem_end && !carried {
                plan.reloc_consts.entry(fi).or_default().push(op);
                fallback.insert((acc.func, acc.op), c);
            }
        }
        for v in plan.reloc_consts.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        // The #1580 folds the selector will apply: an access they cover is
        // relocated by its own effective address.
        let mut folded: std::collections::HashSet<(u32, usize)> = Default::default();
        for (&fi, ops) in inp.func_ops {
            let rel: std::collections::HashSet<usize> = plan
                .reloc_consts
                .get(&fi)
                .map(|v| v.iter().copied().collect())
                .unwrap_or_default();
            for (_, idx, _) in npa_offset_folds(
                ops,
                inp.stack_pointer.map(|(_, v)| v),
                inp.memory0_bytes,
                &rel,
            ) {
                folded.insert((fi, idx));
            }
        }
        // #739: with a stack-pointer global a memarg offset at or above its
        // init is relocated ON ITS OWN by the access (unless a #1580 fold
        // made it part of the constant): it must not double a relocated
        // constant, and the bytes it is retargeted by must be one region.
        let off_relocated = |acc: &M0Access| {
            sp_init.is_some_and(|sp| acc.offset != 0 && acc.offset >= sp)
                && acc.width.is_some()
                && !folded.contains(&(acc.func, acc.op))
        };
        for acc in &f.accesses {
            if !off_relocated(acc) {
                continue;
            }
            let s = &sum[acc.addr];
            if !s.spz.is_empty() || s.spz_many || s.sites.iter().any(|k| relocated.contains(k)) {
                return Err(format!(
                    "npa-double-relocation (#1580): --native-pointer-abi refused for the \
                     whole module — function '{}' (wasm function index {}): {} at op {} adds \
                     the memarg offset 0x{:x}, which is relocated on its own, to an address \
                     that already carries a relocated static constant, so the native address \
                     would count `__synth_wasm_data` twice. No object is written. Fold the \
                     offset into the constant, address it positionally, or drop \
                     --native-pointer-abi.",
                    name(acc.func),
                    acc.func,
                    acc.what,
                    acc.op,
                    acc.offset
                ));
            }
            if !split {
                continue;
            }
            let w = acc.width.unwrap_or(1);
            let (ea, last) = (
                u64::from(acc.offset),
                u64::from(acc.offset) + u64::from(w) - 1,
            );
            let first_r = region_of(ea);
            if let Some(other) = segs
                .iter()
                .flat_map(|&(_, o, b)| [u64::from(o), u64::from(o) + b.len() as u64])
                .filter(|&b| ea < b && b <= last)
                .map(region_of)
                .find(|r| *r != first_r)
            {
                return Err(format!(
                    "npa-region-straddle (#1604): --native-pointer-abi refused for the whole \
                     module — function '{}' (wasm function index {}): {} at op {} relocates \
                     its memarg offset 0x{:x} on its own (a run-time base, #739); the {w} \
                     byte(s) [0x{ea:x}, 0x{:x}) it is retargeted by, which span {} and {}, \
                     are not laid out contiguously by the relocatable object, so the access \
                     would silently read or write the wrong bytes. No object is written. \
                     Keep the access inside one region, merge the data segments it touches \
                     into one segment that covers every byte, or drop --native-pointer-abi.",
                    name(acc.func),
                    acc.func,
                    acc.what,
                    acc.op,
                    acc.offset,
                    last + 1,
                    region_name(first_r),
                    region_name(other),
                ));
            }
        }
        // Every constant-only memory-0 address: relocated, inside ONE region.
        for acc in pure {
            let s = &sum[acc.addr];
            let Vals::Known(vals) = &s.vals else { continue };
            let positional = consts_by_node.contains_key(&acc.addr);
            let width: Option<u32> = match (acc.width, acc.len.map(|l| &sum[l].vals)) {
                (Some(w), _) => Some(w),
                (None, Some(Vals::Known(ls))) => ls.iter().max().copied(),
                _ => None,
            };
            for &v in vals {
                let Some(ea) = v.checked_add(acc.offset) else {
                    continue;
                };
                if u64::from(ea) >= mem_end || ea < pure_lo {
                    // Beyond memory 0 (a native / MMIO address), or the
                    // shadow-stack zone below every static.
                    continue;
                }
                // A #1580 fold makes the constant the effective address, and
                // the constant it rewrites is relocated (the #237 window, or
                // this decision).
                let carried = fallback.contains_key(&(acc.func, acc.op))
                    || folded.contains(&(acc.func, acc.op))
                    || off_relocated(acc)
                    || !s.spz.is_empty()
                    || s.spz_many
                    || s.sites.iter().any(|k| relocated.contains(k));
                if !carried {
                    return Err(format!(
                        "npa-static-unrelocatable (#1568): --native-pointer-abi refused for \
                         the whole module — function '{}' (wasm function index {}): {} at op \
                         {} addresses the constant static address 0x{ea:x}, computed from \
                         constants none of which can carry the relocation. It would be \
                         emitted as a raw address off R11 = 0 and silently read or write \
                         absolute 0x{ea:x}. No object is written. Address the static through \
                         a constant at or above it, or drop --native-pointer-abi.",
                        name(acc.func),
                        acc.func,
                        acc.what,
                        acc.op
                    ));
                }
                if !split {
                    continue;
                }
                let Some(w) = width else {
                    return Err(format!(
                        "npa-region-straddle (#1604): --native-pointer-abi refused for the \
                         whole module — function '{}' (wasm function index {}): {} at op {} \
                         starts at the constant static address 0x{ea:x} with a length \
                         computed at run time. The relocatable object does not lay memory 0 \
                         out contiguously (the reservation is a .bss; each data segment is \
                         packed 4-aligned into .data), so the bytes past 0x{ea:x} need not \
                         be the ones wasm addresses. No object is written. Use a constant \
                         length that stays inside one region, or drop --native-pointer-abi.",
                        name(acc.func),
                        acc.func,
                        acc.what,
                        acc.op
                    ));
                };
                if w == 0 {
                    continue;
                }
                let last = u64::from(ea) + u64::from(w) - 1;
                let first_r = region_of(u64::from(ea));
                let crossing = segs
                    .iter()
                    .flat_map(|&(_, o, b)| [u64::from(o), u64::from(o) + b.len() as u64])
                    .filter(|&b| u64::from(ea) < b && b <= last)
                    .map(region_of)
                    .find(|r| *r != first_r);
                // The relocated constant is retargeted by ITS region — unless
                // the #1580 fold made it the effective address, or the access
                // has no offset and the constant IS the address.
                let base_r =
                    if folded.contains(&(acc.func, acc.op)) || (positional && acc.offset == 0) {
                        None
                    } else {
                        s.sites
                            .iter()
                            .filter(|k| relocated.contains(k))
                            .map(|&k| sites[k].value)
                            .chain(s.spz.iter().copied())
                            .chain(fallback.get(&(acc.func, acc.op)).copied())
                            .chain(off_relocated(acc).then_some(acc.offset))
                            .map(|b| region_of(u64::from(b)))
                            .find(|r| *r != first_r)
                    };
                if let Some(other) = crossing.or(base_r) {
                    return Err(format!(
                        "npa-region-straddle (#1604): --native-pointer-abi refused for the \
                         whole module — function '{}' (wasm function index {}): {} at op {} \
                         touches the {w} byte(s) [0x{ea:x}, 0x{:x}) of a constant address, \
                         which span {} and {} (or whose relocated constant names the \
                         second). The relocatable object does not lay these out \
                         contiguously (the reservation is a .bss; each segment is packed \
                         4-aligned into .data), and the relocation follows one region, so \
                         the access would silently read or write the wrong bytes. No \
                         object is written. Keep the access inside one region, merge the \
                         data segments it touches into one segment that covers every \
                         byte, or drop --native-pointer-abi.",
                        name(acc.func),
                        acc.func,
                        acc.what,
                        acc.op,
                        last + 1,
                        region_name(first_r),
                        region_name(other),
                    ));
                }
            }
        }
        // A static constant dereferenced only after a round trip through
        // memory or a global was stored raw.
        for (k, site) in sites.iter().enumerate() {
            if base_role.contains(&k)
                || offset_role.contains(&k)
                || g.taint[site.node] & 1 == 0
                || !in_zone(u64::from(site.value), 1)
                || obs[site.node]
            {
                continue;
            }
            if let Some(op) = site.op {
                return Err(format!(
                    "npa-static-unrelocatable (#1568): --native-pointer-abi refused for the \
                     whole module — in function '{}' (wasm function index {}) the constant \
                     0x{:x} at op {op} lies in the static region [0x{zlo:x}, 0x{zhi:x}) and \
                     reaches a memory-0 address only through memory or a global, where synth \
                     cannot tell a stored pointer from a stored scalar. No object is written. \
                     Give the module a stack-pointer global placed below its data, or drop \
                     --native-pointer-abi.",
                    name(site.func),
                    site.func,
                    site.value
                ));
            }
        }
        Ok(plan)
    }
}

/// The little-endian word the runtime image holds at `a` (later segments win).
fn word_at(segs: &[(u32, Vec<u8>)], a: u32) -> Option<u32> {
    let mut w = [0u8; 4];
    for (k, b) in w.iter_mut().enumerate() {
        let addr = a.checked_add(k as u32)?;
        *b = segs
            .iter()
            .rev()
            .find(|(o, d)| addr >= *o && u64::from(addr - o) < d.len() as u64)
            .map(|(o, d)| d[(addr - o) as usize])?;
    }
    Some(u32::from_le_bytes(w))
}

#[cfg(test)]
mod tests {
    use super::*;
    use WasmOp::*;

    fn module<'a>(funcs: Vec<NpaFunc<'a>>, args: &'a [u32], res: &'a [u32]) -> NpaModule<'a> {
        NpaModule {
            funcs,
            num_imported_funcs: 0,
            func_arg_counts: args,
            func_result_counts: res,
            type_arg_counts: &[],
            type_result_counts: &[],
            elem_func_indices: &[],
            memory_count: 2,
            cross_copies_carry_no_pointers: false,
        }
    }

    fn mm(op: WasmOp) -> WasmOp {
        MultiMemory {
            memory: 1,
            op: Box::new(op),
        }
    }

    const LD: WasmOp = I32Load {
        offset: 0,
        align: 2,
    };

    #[test]
    fn memory_k_const_stays_raw_and_memory0_const_is_untouched() {
        let f0 = [I32Const(0x2000), mm(LD.clone()), End];
        let f1 = [I32Const(0x2000), LD.clone(), End];
        let m = module(
            vec![
                NpaFunc {
                    index: 0,
                    ops: &f0,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 1,
                    exported: false,
                },
                NpaFunc {
                    index: 1,
                    ops: &f1,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 1,
                    exported: false,
                },
            ],
            &[0, 0],
            &[1, 1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let g = [NpaGlobal {
            index: 0,
            mutable: true,
            init_i32: Some(0x1000),
        }];
        let plan = plan(&p, &g, 0x10000).unwrap();
        assert_eq!(plan.stack_pointer_global, Some((0, 0x1000)));
        assert_eq!(plan.raw_consts.get(&0), Some(&vec![0]));
        assert!(!plan.raw_consts.contains_key(&1));
    }

    #[test]
    fn a_constant_used_in_both_memories_is_refused() {
        // Through a local and a call: f0 stores the pointer, passes it to f1
        // which reads memory 1 through it, and reads memory 0 itself.
        let f0 = [
            I32Const(0x2000),
            LocalSet(0),
            LocalGet(0),
            Call(1),
            Drop,
            LocalGet(0),
            LD.clone(),
            End,
        ];
        let f1 = [LocalGet(0), mm(LD.clone()), End];
        let m = module(
            vec![
                NpaFunc {
                    index: 0,
                    ops: &f0,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 1,
                    exported: false,
                },
                NpaFunc {
                    index: 1,
                    ops: &f1,
                    block_arity: &[],
                    param_count: 1,
                    result_count: 1,
                    exported: false,
                },
            ],
            &[0, 1],
            &[1, 1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let g = [NpaGlobal {
            index: 0,
            mutable: true,
            init_i32: Some(0x1000),
        }];
        let e = plan(&p, &g, 0x10000).unwrap_err();
        assert!(e.contains("function 0 op 0") && e.contains("[1]"), "{e}");
    }

    #[test]
    fn a_pointer_laundered_through_memory_is_tracked() {
        // store 0x2000 into memory 0, load it back, use it in memory 1.
        let st = I32Store {
            offset: 0,
            align: 2,
        };
        let f0 = [
            I32Const(0x10),
            I32Const(0x2000),
            st,
            I32Const(0x10),
            LD.clone(),
            mm(LD.clone()),
            End,
        ];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 0,
                result_count: 1,
                exported: false,
            }],
            &[0],
            &[1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let (c, r) = p.const_at(0, 1).unwrap();
        assert_eq!(c, 0x2000);
        assert_eq!(r.memories_k(), vec![1]);
    }

    #[test]
    fn the_other_domains_stack_pointer_is_not_picked() {
        // global 0 = memory-0 SP (0x1000), global 1 = memory-1 SP (0x8000):
        // the larger init would win the single-memory rule.
        let f0 = [
            GlobalGet(0),
            LD.clone(),
            GlobalGet(1),
            mm(LD.clone()),
            I32Add,
            End,
        ];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 0,
                result_count: 1,
                exported: false,
            }],
            &[0],
            &[1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let g = [
            NpaGlobal {
                index: 0,
                mutable: true,
                init_i32: Some(0x1000),
            },
            NpaGlobal {
                index: 1,
                mutable: true,
                init_i32: Some(0x8000),
            },
        ];
        let plan = plan(&p, &g, 0x10000).unwrap();
        assert_eq!(plan.stack_pointer_global, Some((0, 0x1000)));
        assert_eq!(plan.excluded_stack_pointers, vec![(1, 0x8000, vec![1])]);
    }

    #[test]
    fn a_stack_pointer_used_in_both_memories_is_refused() {
        let f0 = [
            GlobalGet(0),
            LD.clone(),
            GlobalGet(0),
            mm(LD.clone()),
            I32Add,
            End,
        ];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 0,
                result_count: 1,
                exported: false,
            }],
            &[0],
            &[1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let g = [NpaGlobal {
            index: 0,
            mutable: true,
            init_i32: Some(0x1000),
        }];
        assert!(plan(&p, &g, 0x10000).unwrap_err().contains("global 0"));
    }

    #[test]
    fn branch_values_and_compares_carry_reach() {
        // block (result i32) 0x2000 br 0 end -> memory-1 address; and a
        // compare couples 0x3000 with a memory-1 pointer.
        let f0 = [
            Block,
            I32Const(0x2000),
            Br(0),
            End,
            LocalTee(0),
            mm(LD.clone()),
            Drop,
            LocalGet(0),
            I32Const(0x3000),
            I32LtU,
            End,
        ];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[(0, 1)],
                param_count: 0,
                result_count: 1,
                exported: false,
            }],
            &[0],
            &[1],
        );
        let p = Provenance::analyze(&m).unwrap();
        assert_eq!(p.const_at(0, 1).unwrap().1.memories_k(), vec![1]);
        assert_eq!(p.const_at(0, 8).unwrap().1.memories_k(), vec![1]);
    }

    #[test]
    fn a_host_parameter_used_in_both_memories_is_refused() {
        let f0 = [
            LocalGet(0),
            LD.clone(),
            LocalGet(0),
            mm(LD.clone()),
            I32Add,
            End,
        ];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 1,
                result_count: 1,
                exported: true,
            }],
            &[1],
            &[1],
        );
        let p = Provenance::analyze(&m).unwrap();
        let e = plan(&p, &[], 0x10000).unwrap_err();
        assert!(e.contains("parameter 0 of exported function 0"), "{e}");
    }

    #[test]
    fn a_cross_memory_copy_charges_each_side_to_its_memory() {
        // memory.copy $m1 $m0 (0x3000, 0x2000, 4): dst is a memory-1
        // address, src a memory-0 address.
        let cp = MultiMemory {
            memory: 1,
            op: Box::new(MemoryCopyBetween {
                dst_mem: 1,
                src_mem: 0,
            }),
        };
        let f0 = [I32Const(0x3000), I32Const(0x2000), I32Const(4), cp, End];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 0,
                result_count: 0,
                exported: false,
            }],
            &[0],
            &[0],
        );
        let p = Provenance::analyze(&m).unwrap();
        let (_, dst) = p.const_at(0, 0).unwrap();
        let (_, src) = p.const_at(0, 1).unwrap();
        assert!(!dst.memory0() && dst.memories_k() == vec![1]);
        assert!(src.memory0() && src.memories_k().is_empty());
    }

    #[test]
    fn the_cross_copy_assertion_stops_the_contents_join_and_nothing_else() {
        // f0 stores 0x2000 in memory 0 and reads through it there; f1 follows
        // a pointer stored in memory 1; f2 copies memory 0 -> memory 1.
        let st = I32Store {
            offset: 0,
            align: 2,
        };
        let cp = MultiMemory {
            memory: 1,
            op: Box::new(MemoryCopyBetween {
                dst_mem: 1,
                src_mem: 0,
            }),
        };
        let f0 = [
            I32Const(0x10),
            I32Const(0x2000),
            st,
            I32Const(0x10),
            LD.clone(),
            LD.clone(),
            End,
        ];
        let f1 = [I32Const(0x10), mm(LD.clone()), mm(LD.clone()), End];
        let f2 = [I32Const(0), I32Const(0), I32Const(4), cp, End];
        for assert_flag in [false, true] {
            let funcs = vec![
                NpaFunc {
                    index: 0,
                    ops: &f0,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 1,
                    exported: false,
                },
                NpaFunc {
                    index: 1,
                    ops: &f1,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 1,
                    exported: false,
                },
                NpaFunc {
                    index: 2,
                    ops: &f2,
                    block_arity: &[],
                    param_count: 0,
                    result_count: 0,
                    exported: false,
                },
            ];
            let mut m = module(funcs, &[0, 0, 0], &[1, 1, 0]);
            m.cross_copies_carry_no_pointers = assert_flag;
            let p = Provenance::analyze(&m).unwrap();
            let (_, r) = p.const_at(0, 1).unwrap();
            assert_eq!(r.memories_k().is_empty(), assert_flag, "flag={assert_flag}");
            assert_eq!(p.joined_by_cross_copy(), !assert_flag);
        }
    }

    #[test]
    fn an_unmodeled_op_is_an_error_not_a_guess() {
        let f0 = [V128Const([0; 16]), I8x16Splat, End];
        let m = module(
            vec![NpaFunc {
                index: 0,
                ops: &f0,
                block_arity: &[],
                param_count: 0,
                result_count: 0,
                exported: false,
            }],
            &[0],
            &[0],
        );
        assert!(Provenance::analyze(&m).is_err());
    }
}
