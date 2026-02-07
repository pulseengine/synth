*** Settings ***
Documentation     WAST-driven i32 arithmetic tests for Synth
...               Auto-generated from i32_arithmetic.wast pattern

*** Variables ***
${PLATFORM}    ${CURDIR}/../renode/synth_cortex_m.repl
${FUNC_ADDR}    0x91

*** Keywords ***
Create Cortex-M Machine
    Execute Command    mach create "synth-wast-test"
    Execute Command    machine LoadPlatformDescription @${PLATFORM}

To Unsigned
    [Arguments]    ${value}
    ${unsigned}=    Evaluate    int(${value}) & 0xFFFFFFFF
    [Return]    ${unsigned}

To Signed
    [Arguments]    ${value}
    ${clean}=    Evaluate    int(str(${value}).strip())
    ${signed}=    Evaluate    ${clean} if ${clean} < 0x80000000 else ${clean} - 0x100000000
    [Return]    ${signed}

Execute Add Function
    [Arguments]    ${a}    ${b}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${ELF}"
    Execute Command    cpu PC ${FUNC_ADDR}
    # Convert signed to unsigned (handles negative numbers)
    ${a_unsigned}=    To Unsigned    ${a}
    ${b_unsigned}=    To Unsigned    ${b}
    # Set arguments in r0 and r1 per AAPCS
    Execute Command    cpu SetRegisterUnsafe 0 ${a_unsigned}
    Execute Command    cpu SetRegisterUnsafe 1 ${b_unsigned}
    # Execute function (ADD r0,r0,r1; BX lr = 2 instructions)
    Execute Command    cpu Step 2
    ${result}=    Execute Command    cpu GetRegisterUnsafe 0
    # Convert result back to signed for comparison
    ${result_signed}=    To Signed    ${result}
    [Return]    ${result_signed}

*** Test Cases ***
WAST add_1 - Basic addition 5+3=8
    [Documentation]    assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8)
    ${result}=    Execute Add Function    5    3
    Should Be Equal As Integers    ${result}    8    msg=add(5,3) should return 8

WAST add_2 - Zero addition 0+0=0
    [Documentation]    assert_return (invoke "add" (i32.const 0) (i32.const 0)) (i32.const 0)
    ${result}=    Execute Add Function    0    0
    Should Be Equal As Integers    ${result}    0    msg=add(0,0) should return 0

WAST add_3 - Additive inverse 1+-1=0
    [Documentation]    assert_return (invoke "add" (i32.const 1) (i32.const -1)) (i32.const 0)
    ${result}=    Execute Add Function    1    -1
    Should Be Equal As Integers    ${result}    0    msg=add(1,-1) should return 0

WAST add_4 - Larger numbers 100+200=300
    [Documentation]    assert_return (invoke "add" (i32.const 100) (i32.const 200)) (i32.const 300)
    ${result}=    Execute Add Function    100    200
    Should Be Equal As Integers    ${result}    300    msg=add(100,200) should return 300

WAST add_5 - Negative addition -5+-3=-8
    [Documentation]    assert_return (invoke "add" (i32.const -5) (i32.const -3)) (i32.const -8)
    ${result}=    Execute Add Function    -5    -3
    Should Be Equal As Integers    ${result}    -8    msg=add(-5,-3) should return -8
