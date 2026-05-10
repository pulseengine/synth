*** Settings ***
Documentation     Cortex-M7 ELF execution test for Synth-generated binaries
...               Validates that Synth's M7 codegen path emits a correctly
...               structured ELF that loads and executes on a 16-MPU-region
...               M7-class platform with single-precision FPU.

*** Variables ***
${PLATFORM}                         ${CURDIR}/synth_cortex_m7.repl

*** Keywords ***
Create Cortex-M7 Machine
    Execute Command                 mach create "synth-m7-test"
    Execute Command                 machine LoadPlatformDescription @${PLATFORM}

*** Test Cases ***
Should Load And Execute Simple Add Function On M7
    [Documentation]                 Synth-generated --target cortex-m7 ELF executes correctly
    Create Cortex-M7 Machine

    Execute Command                 sysbus LoadELF "${ELF}"

    # The add function lives at 0xA0 (user code, after 28-byte startup + handlers)
    Execute Command                 cpu PC 0xA1

    # AAPCS: r0 = 5, r1 = 3, expected result = 8
    Execute Command                 cpu SetRegisterUnsafe 0 5
    Execute Command                 cpu SetRegisterUnsafe 1 3

    Execute Command                 cpu Step 2

    ${r0}=                          Execute Command  cpu GetRegisterUnsafe 0
    Should Be Equal As Integers     ${r0}  8  msg=Expected r0 to be 8 (5+3) on M7
