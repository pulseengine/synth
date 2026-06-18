/* #359 post-link oracle: mimic the Zephyr layout that gave rc=-35.
   __synth_wasm_seg_0 (.data, real table) at 0x20000000; __synth_wasm_data
   (.bss, zero reservation) right after .data — matching gale's objdump
   (seg_0=0x20000000, __synth_wasm_data==__bss_start). */
MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K
         RAM  (rwx) : ORIGIN = 0x20000000, LENGTH = 256K }
SECTIONS {
  .text : { *(.text*) } > FLASH
  .data : { *(.data*) } > RAM
  __bss_start = .;
  .bss  : { *(.bss*) } > RAM
  __bss_end = .;
}
