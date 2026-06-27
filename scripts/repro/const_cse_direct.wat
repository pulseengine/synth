;; VCR-RA const-CSE (#242) — DIRECT-PATH (`--relocatable`) trigger fixtures.
;;
;; gale's gust_mix 90->92 B regression was on `--relocatable`, which routes
;; through the direct selector (`select_direct`) — there the optimized path's
;; INLINE const cache never runs, so the post-hoc `liveness::apply_const_cse`
;; acts ALONE. The main `const_cse.wat` corpus is INERT on that path (its
;; arithmetic shapes don't make the direct selector materialize the same value
;; into two distinct live registers in one straight-line segment), so it gave no
;; positive evidence the no-regression fix actually engages gale's path.
;;
;; These shapes DO make the direct selector emit the redundant materialization
;; that `apply_const_cse` then dedups: a >8-bit const (needs `movw`) reused across
;; several independent sub-expressions whose results stay live to a final sum.
;; All are single-param, pure-register (no memory) so they link with zero
;; relocations and run directly under unicorn (R0=arg) for a correctness check vs
;; wasmtime. CSE fires (each shrinks) on `--relocatable`, so the differential's
;; direct-path gate is non-vacuous: it proves post-hoc CSE engages gale's path,
;; stays correct, and never grows a function.
(module
  (memory 1)

  ;; one const (30011) reused by four independent ops, all summed.
  (func (export "r1") (param i32) (result i32)
    (i32.add
      (i32.add (i32.mul (local.get 0) (i32.const 30011)) (i32.xor (local.get 0) (i32.const 30011)))
      (i32.add (i32.and (local.get 0) (i32.const 30011)) (i32.or  (local.get 0) (i32.const 30011)))))

  ;; same const (50021) reused by three ops, summed — different op mix.
  (func (export "r2") (param i32) (result i32)
    (i32.add
      (i32.add (i32.mul (local.get 0) (i32.const 50021)) (i32.sub (local.get 0) (i32.const 50021)))
      (i32.xor (local.get 0) (i32.const 50021))))

  ;; NEGATIVE const (-30013) — exercises the movw/movt reconstruction path in
  ;; const_materialization (keyed by u32 bit-pattern).
  (func (export "rneg") (param i32) (result i32)
    (i32.add
      (i32.add (i32.mul (local.get 0) (i32.const -30013)) (i32.xor (local.get 0) (i32.const -30013)))
      (i32.and (local.get 0) (i32.const -30013))))
)
