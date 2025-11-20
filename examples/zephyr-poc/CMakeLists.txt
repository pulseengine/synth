# Synth WASM Compiler - Zephyr POC
#
# Demonstrates WASM function compiled to ARM and linked with Zephyr

cmake_minimum_required(VERSION 3.20.0)

find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(synth_wasm_poc)

# Main application
target_sources(app PRIVATE src/main.c)

# Link with Synth-compiled WASM function
target_sources(app PRIVATE src/add.s)
