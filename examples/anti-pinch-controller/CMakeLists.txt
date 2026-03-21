# Anti-Pinch Window Controller -- Synth WASM Compiler Demo
#
# Safety-critical automotive use case: anti-pinch protection via
# motor current monitoring. All control logic compiled from WebAssembly
# using formally verified Synth compiler.

cmake_minimum_required(VERSION 3.20.0)

find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(synth_anti_pinch)

# Main Zephyr application (simulates motor/window system)
target_sources(app PRIVATE src/main.c)

# Synth-compiled WASM control functions (anti_pinch.wat -> ARM Thumb-2)
# These are compiled using formally verified instruction selection.
# In production, generate this file with:
#   synth compile anti_pinch.wat -o anti_pinch.s --cortex-m --all-exports
target_sources(app PRIVATE src/anti_pinch.s)
