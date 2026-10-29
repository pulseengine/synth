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
}

impl Graph {
    fn fresh(&mut self) -> Node {
        self.preds.push(Vec::new());
        self.taint.push(0);
        self.preds.len() - 1
    }
    fn keyed<K: std::hash::Hash + Eq>(
        map: &mut HashMap<K, Node>,
        k: K,
        g: &mut Vec<Vec<Node>>,
        t: &mut Vec<Mask>,
    ) -> Node {
        *map.entry(k).or_insert_with(|| {
            g.push(Vec::new());
            t.push(0);
            g.len() - 1
        })
    }
    fn local(&mut self, f: u32, l: u32) -> Node {
        Self::keyed(&mut self.locals, (f, l), &mut self.preds, &mut self.taint)
    }
    fn ret(&mut self, f: u32, r: u32) -> Node {
        Self::keyed(&mut self.rets, (f, r), &mut self.preds, &mut self.taint)
    }
    fn global(&mut self, g: u32) -> Node {
        Self::keyed(&mut self.globals, g, &mut self.preds, &mut self.taint)
    }
    fn mem(&mut self, m: u32) -> Node {
        Self::keyed(&mut self.mems, m, &mut self.preds, &mut self.taint)
    }
    /// The value of `from` flows into `to`.
    fn flow(&mut self, from: Node, to: Node) {
        if from != to {
            self.preds[to].push(from);
        }
    }
    /// `a` and `b` must share one representation.
    fn couple(&mut self, a: Node, b: Node) {
        self.flow(a, b);
        self.flow(b, a);
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
                    pop(g, &mut stack, &frames, i)?;
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
                pop(g, &mut stack, &frames, i)?;
                label_flow(g, &stack, &frames, *l, i)?;
            }
            BrTable { targets, default } => {
                pop(g, &mut stack, &frames, i)?;
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
                    for r in 0..resc {
                        let n = g.fresh();
                        g.host_entries.push((
                            format!("result {r} of the host call at function {fi} op {i}"),
                            n,
                        ));
                        stack.push(n);
                    }
                }
            }
            CallIndirect { type_index, .. } => {
                pop(g, &mut stack, &frames, i)?; // table index (a scalar)
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
                pop(g, &mut stack, &frames, i)?;
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
            }
            MemoryCopyBetween { dst_mem, src_mem } => {
                // #1145: a cross-/non-default-memory copy. Each address is
                // charged to its own memory, and the copied BYTES flow from
                // the source memory's contents into the destination's — so
                // a pointer carried across memories is still tracked (and,
                // field-insensitively, the two memories' contents join).
                pop(g, &mut stack, &frames, i)?; // len
                let src = pop(g, &mut stack, &frames, i)?;
                let dst = pop(g, &mut stack, &frames, i)?;
                g.address(dst, *dst_mem)?;
                g.address(src, *src_mem)?;
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
                pop(g, &mut stack, &frames, i)?; // len
                let src_or_val = pop(g, &mut stack, &frames, i)?;
                let dst = pop(g, &mut stack, &frames, i)?;
                g.address(dst, 0)?;
                let content = g.mem(0);
                if matches!(inner, MemoryCopy) {
                    g.address(src_or_val, 0)?;
                } else {
                    g.flow(src_or_val, content);
                }
            }
            MemorySize(_) => {
                let n = g.fresh();
                stack.push(n);
            }
            MemoryGrow(_) => {
                pop(g, &mut stack, &frames, i)?;
                let n = g.fresh();
                stack.push(n);
            }
            I32Eq | I32Ne | I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS
            | I32GeU | I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU
            | I64GeS | I64GeU => {
                let b = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                g.couple(a, b);
                let n = g.fresh();
                stack.push(n);
            }
            I32Sub | I64Sub => {
                let b = pop(g, &mut stack, &frames, i)?;
                let a = pop(g, &mut stack, &frames, i)?;
                g.couple(a, b);
                let r = g.fresh();
                g.flow(a, r);
                g.flow(b, r);
                stack.push(r);
            }
            other if memory == 0 => {
                let Some((pops, pushes)) = fixed_stack_effect(other) else {
                    return Err(format!(
                        "op {i}: {other:?} is not modeled by the provenance pass"
                    ));
                };
                let ins = pop_n(g, &mut stack, &frames, pops as usize, i)?;
                for _ in 0..pushes {
                    let r = g.fresh();
                    for &v in &ins {
                        g.flow(v, r);
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
