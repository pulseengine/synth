#!/bin/bash
# Download Bazel dependencies manually using curl (bypasses Bazel proxy issues)

set -e

DISTDIR="${HOME}/bazel_distdir"
mkdir -p "$DISTDIR"

echo "Downloading Bazel dependencies to $DISTDIR..."
echo "This uses curl which works with the git gateway proxy."
echo ""

# Dependencies from MODULE.bazel
DEPS=(
    # Core Bazel dependencies
    "https://github.com/bazelbuild/platforms/releases/download/0.0.10/platforms-0.0.10.tar.gz"
    "https://github.com/bazelbuild/bazel-skylib/releases/download/1.7.1/bazel-skylib-1.7.1.tar.gz"
    "https://github.com/bazelbuild/rules_rust/releases/download/0.54.1/rules_rust-v0.54.1.tar.gz"

    # Rust crates (crates_io will be fetched separately)
    # These are handled by crate_universe extension
)

for url in "${DEPS[@]}"; do
    filename=$(basename "$url")
    echo "Downloading $filename..."

    if [ -f "$DISTDIR/$filename" ]; then
        echo "  Already exists, skipping."
    else
        curl -L "$url" -o "$DISTDIR/$filename"
        echo "  ✓ Downloaded"
    fi
done

echo ""
echo "✓ All dependencies downloaded!"
echo ""
echo "To use with Bazel:"
echo "  bazel build --distdir=$DISTDIR //..."
echo ""
echo "Or add to .bazelrc.local:"
echo "  build --distdir=$DISTDIR"
echo "  fetch --distdir=$DISTDIR"
