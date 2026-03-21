# Synth WASM Compiler - Zephyr Calculator
#
# Demonstrates 14 WASM functions compiled to ARM Thumb-2 assembly
# and linked into a Zephyr RTOS application.

cmake_minimum_required(VERSION 3.20.0)

find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(synth_calculator)

# Main application
target_sources(app PRIVATE src/main.c)

# Synth-compiled WASM functions (ARM Thumb-2 assembly)
target_sources(app PRIVATE src/calculator.s)
