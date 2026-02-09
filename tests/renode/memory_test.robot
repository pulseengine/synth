*** Settings ***
Documentation     Memory load/store test for Synth-generated binaries
...               Tests that R11-based linear memory addressing works correctly

*** Variables ***
${PLATFORM}                         ${CURDIR}/synth_cortex_m.repl
${RETURN_TRAP}                      0x9C

*** Keywords ***
Create Cortex-M Machine
    Execute Command                 mach create "memory-test"
    Execute Command                 machine LoadPlatformDescription @${PLATFORM}

To Unsigned
    [Arguments]                     ${value}
    ${unsigned}=                    Evaluate    int(${value}) & 0xFFFFFFFF
    [Return]                        ${unsigned}

To Signed
    [Arguments]                     ${value}
    ${clean}=                       Evaluate    int(str(${value}).strip())
    ${signed}=                      Evaluate    ${clean} if ${clean} < 0x80000000 else ${clean} - 0x100000000
    [Return]                        ${signed}

Execute Memory Function
    [Documentation]                 Execute a function with R11 set to linear memory base
    [Arguments]                     ${func_addr}  @{args}
    Create Cortex-M Machine
    Execute Command                 sysbus LoadELF "${ELF}"
    Execute Command                 cpu PC ${func_addr}
    # Set SP (R13) to top of RAM
    Execute Command                 cpu SetRegisterUnsafe 13 0x20020000
    # Set R10 to memory size (64KB = 0x10000) for bounds checking
    Execute Command                 cpu SetRegisterUnsafe 10 0x10000
    # Set R11 to linear memory base (0x20000000) - matches startup code
    Execute Command                 cpu SetRegisterUnsafe 11 0x20000000
    # Set LR (R14) to Default_Handler | 1 so BX LR goes to infinite loop
    ${lr}=                          Evaluate    ${RETURN_TRAP} | 1
    Execute Command                 cpu SetRegisterUnsafe 14 ${lr}
    # Set arguments in r0-r3 per AAPCS (convert to unsigned for Renode)
    ${reg}=                         Set Variable    0
    FOR    ${arg}    IN    @{args}
        ${arg_unsigned}=            To Unsigned    ${arg}
        Execute Command             cpu SetRegisterUnsafe ${reg} ${arg_unsigned}
        ${reg}=                     Evaluate    ${reg} + 1
    END
    # Step generous maximum; function returns into Default_Handler well before this
    Execute Command                 cpu Step 5000
    # Verify function returned: PC should be at Default_Handler (infinite loop)
    ${pc_raw}=                      Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=                          Evaluate    int(str(${pc_raw}).strip())
    Should Be Equal As Integers     ${pc}    ${RETURN_TRAP}    msg=Function did not return within 5000 steps (PC=0x${pc.__format__('X')})
    # Return R0 as signed integer
    ${result}=                      Execute Command  cpu GetRegisterUnsafe 0
    ${result_signed}=               To Signed    ${result}
    [Return]                        ${result_signed}

*** Test Cases ***
Should Store And Load At Address Zero
    [Documentation]                 Test fixed_test: store 42 at addr 0, load it back
    # fixed_test is at 0xC0, call with Thumb bit (0xC1)
    ${result}=                      Execute Memory Function  0xC1
    Should Be Equal As Integers     ${result}  42  msg=Expected 42 from fixed_test: ${result}

Should Store And Load With Parameters
    [Documentation]                 Test store_load(addr=100, value=0x12345678) -> 0x12345678
    # store_load is at 0xA0, call with Thumb bit (0xA1)
    ${result}=                      Execute Memory Function  0xA1  100  305419896
    Should Be Equal As Integers     ${result}  305419896  msg=Expected 0x12345678 from store_load: ${result}

Should Store And Load With Offset
    [Documentation]                 Test store_load_offset(addr=0, value=0xDEADBEEF) -> 0xDEADBEEF
    # store_load_offset is at 0xAC, call with Thumb bit (0xAD)
    ${result}=                      Execute Memory Function  0xAD  0  -559038737
    Should Be Equal As Integers     ${result}  -559038737  msg=Expected 0xDEADBEEF from store_load_offset: ${result}
