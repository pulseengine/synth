#!/bin/bash
# Script to install Sail toolchain for SPIKE-001
#
# This script installs:
# - OCaml via OPAM
# - Sail compiler
# - Dependencies for Coq generation
#
# Usage: ./install_sail.sh

set -e  # Exit on error

echo "================================================"
echo "SPIKE-001: Installing Sail Toolchain"
echo "================================================"
echo ""

# Check OS
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    OS="linux"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    OS="macos"
else
    echo "Error: Unsupported OS: $OSTYPE"
    exit 1
fi

echo "Detected OS: $OS"
echo ""

# Install system dependencies
echo "Step 1/5: Installing system dependencies..."
if [ "$OS" = "linux" ]; then
    sudo apt-get update
    sudo apt-get install -y \
        opam \
        m4 \
        libgmp-dev \
        z3 \
        build-essential \
        pkg-config
elif [ "$OS" = "macos" ]; then
    brew install opam gmp z3
fi
echo "✓ System dependencies installed"
echo ""

# Initialize OPAM
echo "Step 2/5: Initializing OPAM..."
if [ ! -d "$HOME/.opam" ]; then
    opam init -y --disable-sandboxing
else
    echo "OPAM already initialized"
fi
eval $(opam env)
echo "✓ OPAM initialized"
echo ""

# Create OCaml switch
echo "Step 3/5: Creating OCaml 4.14 switch..."
if ! opam switch list | grep -q "4.14.0"; then
    opam switch create 4.14.0 -y
else
    echo "OCaml 4.14.0 switch already exists"
fi
eval $(opam env)
echo "✓ OCaml switch created"
echo ""

# Install Sail dependencies
echo "Step 4/5: Installing Sail dependencies..."
opam install -y \
    menhir \
    ott \
    lem \
    linksem
echo "✓ Sail dependencies installed"
echo ""

# Install Sail
echo "Step 5/5: Installing Sail compiler..."
opam install -y sail
echo "✓ Sail compiler installed"
echo ""

# Verify installation
echo "================================================"
echo "Verification"
echo "================================================"
echo ""

echo "OCaml version:"
ocaml -version

echo ""
echo "OPAM version:"
opam --version

echo ""
echo "Sail version:"
sail --version

echo ""
echo "================================================"
echo "Installation Complete!"
echo "================================================"
echo ""
echo "To use Sail in a new shell, run:"
echo "  eval \$(opam env)"
echo ""
echo "To generate Coq from Sail:"
echo "  sail -coq input.sail -o output.v"
echo ""
echo "Next steps:"
echo "  cd spike"
echo "  ./scripts/test_sail_coq_gen.sh"
echo ""
