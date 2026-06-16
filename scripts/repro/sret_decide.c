// Mirror gale_k_msgq_put_decide: a 16-byte struct return + 5 scalar args.
// clang --target=wasm32 lowers the struct return to a hidden sret pointer = wasm param0.
typedef struct { int ret; unsigned char action; unsigned new_widx; unsigned new_used; } Decision;

__attribute__((noinline))
Decision decide(unsigned write_idx, unsigned used, unsigned max, int has_waiter, int is_no_wait) {
    Decision d;
    if (used < max) { d.ret = 0;   d.action = 1; d.new_widx = write_idx + 1; d.new_used = used + 1; }
    else            { d.ret = -35; d.action = 0; d.new_widx = write_idx;     d.new_used = used; }
    (void)has_waiter; (void)is_no_wait;
    return d;
}
// Mirror z_impl_k_msgq_put: allocate the buffer, call, read ret back.
int shim(unsigned write_idx, unsigned used, unsigned max) {
    Decision d = decide(write_idx, used, max, 0, 0);
    return d.ret;
}
