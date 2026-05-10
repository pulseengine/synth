*** Settings ***
Documentation     Basic RV32IMAC ELF execution test for Synth-generated binaries.
...               Validates that synth's RISC-V backend produces an ELF whose
...               .text section can be loaded and executed on a SiFive-class
...               RV32IMAC platform with the standard psABI.

*** Variables ***
${PLATFORM}                         ${CURDIR}/synth_riscv.repl

*** Keywords ***
Create RISC-V Machine
    Execute Command                 mach create "synth-rv32-test"
    Execute Command                 machine LoadPlatformDescription @${PLATFORM}

*** Test Cases ***
Should Load And Execute Simple Add Function On RV32
    [Documentation]                 Synth-generated --backend riscv --target riscv32imac
    ...                             ELF executes correctly under emulation. Verifies the
    ...                             RV32IMAC code path for `add(a, b) → a + b`.
    Create RISC-V Machine

    Execute Command                 sysbus LoadELF "${ELF}"

    # Synth's RISC-V selector emits 5 instructions for `add(a,b)`:
    #   addi t0, a0, 0
    #   addi t1, a1, 0
    #   add  t2, t0, t1
    #   addi a0, t2, 0
    #   jalr zero, 0(ra)
    # The first function is at .text offset 0, which the ELF symbol table
    # marks for "add". Place PC there explicitly and step through.
    Execute Command                 cpu PC 0x0

    # psABI: a0 = 5, a1 = 3, expected result = 8
    Execute Command                 cpu SetRegisterUnsafe 10 5
    Execute Command                 cpu SetRegisterUnsafe 11 3
    # ra = 0xFF (a sentinel — the function will return there; we just
    # care the return path is hit, not where it lands)
    Execute Command                 cpu SetRegisterUnsafe 1 0xFF

    # Step through the 5 instructions of the add function.
    Execute Command                 cpu Step 5

    ${a0}=                          Execute Command  cpu GetRegisterUnsafe 10
    Should Be Equal As Integers     ${a0}  8  msg=Expected a0 to be 8 (5+3) on RV32
