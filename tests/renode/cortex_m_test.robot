*** Settings ***
Documentation     Basic Cortex-M ELF execution test for Synth-generated binaries

*** Variables ***
# Custom minimal Cortex-M4 platform for Synth binaries
# Uses memory at 0x0 to match our vector table placement
${PLATFORM}                         ${CURDIR}/synth_cortex_m.repl

*** Keywords ***
Create Cortex-M Machine
    Execute Command                 mach create "synth-test"
    Execute Command                 machine LoadPlatformDescription @${PLATFORM}

*** Test Cases ***
Should Load And Execute Simple Add Function
    [Documentation]                 Test that a Synth-generated ELF loads and executes
    Create Cortex-M Machine

    # Load the ELF binary
    Execute Command                 sysbus LoadELF "${ELF}"

    # The add function is at 0xA0 (user code address, after 28-byte startup + handlers)
    # We call it directly to avoid startup code clobbering r0/r1
    # Set PC to function address with Thumb bit (0xA1)
    Execute Command                 cpu PC 0xA1

    # Set up arguments in r0 and r1 (per AAPCS)
    # r0 = 5, r1 = 3, expected result = 8
    Execute Command                 cpu SetRegisterUnsafe 0 5
    Execute Command                 cpu SetRegisterUnsafe 1 3

    # Step through the add function
    # Our function is: ADD r0, r0, r1; BX lr (2 instructions)
    Execute Command                 cpu Step 2

    # After execution, r0 should contain the result (5 + 3 = 8)
    ${r0}=                          Execute Command  cpu GetRegisterUnsafe 0
    Should Be Equal As Integers     ${r0}  8  msg=Expected r0 to be 8 (5+3)
