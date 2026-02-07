*** Settings ***
Documentation     Memory load/store test for Synth-generated binaries
...               Tests that R11-based linear memory addressing works correctly

*** Variables ***
${PLATFORM}                         ${CURDIR}/synth_cortex_m.repl
${ELF}                              ${CURDIR}/../../build/memory_basic.elf

*** Keywords ***
Create Cortex-M Machine
    Execute Command                 mach create "memory-test"
    Execute Command                 machine LoadPlatformDescription @${PLATFORM}

Execute Function
    [Arguments]                     ${func_addr}  ${r0}=0  ${r1}=0  ${steps}=10
    Execute Command                 cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (128KB)
    Execute Command                 cpu SetRegisterUnsafe 13 0x20020000
    # Set R10 to memory size (64KB = 0x10000) for bounds checking
    Execute Command                 cpu SetRegisterUnsafe 10 0x10000
    # Set R11 to linear memory base (0x20000000) - matches startup code
    Execute Command                 cpu SetRegisterUnsafe 11 0x20000000
    # Set LR (R14) to Default_Handler | 1 so BX LR goes to infinite loop
    # Default_Handler is at 0x9C (after 28-byte startup at 0x80)
    Execute Command                 cpu SetRegisterUnsafe 14 0x9D
    # Set arguments
    Execute Command                 cpu SetRegisterUnsafe 0 ${r0}
    Execute Command                 cpu SetRegisterUnsafe 1 ${r1}
    # Execute
    Execute Command                 cpu Step ${steps}
    # Return R0
    ${result}=                      Execute Command  cpu GetRegisterUnsafe 0
    RETURN                          ${result}

*** Test Cases ***
Should Store And Load At Address Zero
    [Documentation]                 Test fixed_test: store 42 at addr 0, load it back
    Create Cortex-M Machine
    Execute Command                 sysbus LoadELF "${ELF}"

    # fixed_test is at 0xE0, call with Thumb bit (0xE1)
    ${result}=                      Execute Function  0xE1  steps=20

    Should Be Equal As Integers     ${result}  42  msg=Expected 42 from fixed_test

Should Store And Load With Parameters
    [Documentation]                 Test store_load(addr, value) -> value
    Create Cortex-M Machine
    Execute Command                 sysbus LoadELF "${ELF}"

    # store_load is at 0xA0, call with Thumb bit (0xA1)
    # Args: r0=100 (addr), r1=0x12345678 (value)
    ${result}=                      Execute Function  0xA1  r0=100  r1=0x12345678  steps=10

    Should Be Equal As Integers     ${result}  0x12345678  msg=Expected 0x12345678 from store_load

Should Store And Load With Offset
    [Documentation]                 Test store_load_offset(addr, value) -> value (offset=4)
    Create Cortex-M Machine
    Execute Command                 sysbus LoadELF "${ELF}"

    # store_load_offset is at 0xC0, call with Thumb bit (0xC1)
    # Args: r0=0 (base addr), r1=0xDEADBEEF (value)
    # The function stores at addr+4 and loads from addr+4
    ${result}=                      Execute Function  0xC1  r0=0  r1=0xDEADBEEF  steps=15

    Should Be Equal As Integers     ${result}  0xDEADBEEF  msg=Expected 0xDEADBEEF from store_load_offset
