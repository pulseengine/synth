#!/bin/bash
# Install QEMU from source for ARM emulation
# This downloads and builds QEMU instead of using apt

set -e

# Configuration
QEMU_VERSION="8.2.0"
QEMU_URL="https://download.qemu.org/qemu-${QEMU_VERSION}.tar.xz"
INSTALL_DIR="${HOME}/.local"
BUILD_DIR="${HOME}/.cache/qemu-build"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}==================================================${NC}"
echo -e "${GREEN}  QEMU ${QEMU_VERSION} Installation Script${NC}"
echo -e "${GREEN}==================================================${NC}"
echo ""

# Check for required build dependencies
echo -e "${YELLOW}Checking build dependencies...${NC}"
MISSING_DEPS=()

check_command() {
    if ! command -v $1 &> /dev/null; then
        MISSING_DEPS+=($1)
    fi
}

check_command make
check_command gcc
check_command g++
check_command python3
check_command meson
check_command ninja
check_command pkg-config

if [ ${#MISSING_DEPS[@]} -ne 0 ]; then
    echo -e "${RED}Missing dependencies: ${MISSING_DEPS[@]}${NC}"
    echo ""
    echo "Please install them first:"
    echo "  sudo apt-get install build-essential python3-pip ninja-build pkg-config libglib2.0-dev libpixman-1-dev"
    echo "  pip3 install --user meson"
    exit 1
fi

echo -e "${GREEN}All dependencies found!${NC}"
echo ""

# Create build directory
echo -e "${YELLOW}Creating build directory: ${BUILD_DIR}${NC}"
mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"

# Download QEMU if not already downloaded
if [ ! -f "qemu-${QEMU_VERSION}.tar.xz" ]; then
    echo -e "${YELLOW}Downloading QEMU ${QEMU_VERSION}...${NC}"
    wget "${QEMU_URL}" -O "qemu-${QEMU_VERSION}.tar.xz"
    echo -e "${GREEN}Download complete!${NC}"
else
    echo -e "${YELLOW}QEMU ${QEMU_VERSION} archive already exists, skipping download${NC}"
fi

# Extract
echo -e "${YELLOW}Extracting QEMU...${NC}"
tar -xf "qemu-${QEMU_VERSION}.tar.xz"
cd "qemu-${QEMU_VERSION}"

# Configure QEMU for ARM targets only
echo -e "${YELLOW}Configuring QEMU build...${NC}"
echo "  Targets: arm-softmmu, arm-linux-user"
echo "  Install prefix: ${INSTALL_DIR}"
echo ""

./configure \
    --prefix="${INSTALL_DIR}" \
    --target-list=arm-softmmu,arm-linux-user \
    --enable-system \
    --enable-linux-user \
    --disable-docs \
    --disable-gtk \
    --disable-sdl \
    --disable-vnc \
    --enable-pie

# Build
echo ""
echo -e "${YELLOW}Building QEMU (this may take 10-20 minutes)...${NC}"
make -j$(nproc)

# Install
echo ""
echo -e "${YELLOW}Installing QEMU to ${INSTALL_DIR}...${NC}"
make install

# Verify installation
echo ""
echo -e "${GREEN}Verifying installation...${NC}"
"${INSTALL_DIR}/bin/qemu-system-arm" --version

echo ""
echo -e "${GREEN}==================================================${NC}"
echo -e "${GREEN}  QEMU ${QEMU_VERSION} installed successfully!${NC}"
echo -e "${GREEN}==================================================${NC}"
echo ""
echo "QEMU binaries installed to: ${INSTALL_DIR}/bin/"
echo "  - qemu-system-arm (for full system emulation)"
echo "  - qemu-arm (for linux-user emulation)"
echo ""
echo "Add to your PATH:"
echo "  export PATH=\"${INSTALL_DIR}/bin:\$PATH\""
echo ""
echo "Or add to ~/.bashrc:"
echo "  echo 'export PATH=\"${INSTALL_DIR}/bin:\$PATH\"' >> ~/.bashrc"
echo "  source ~/.bashrc"
echo ""
echo "Test QEMU:"
echo "  qemu-system-arm -M help"
echo "  qemu-system-arm -M netduino2 -nographic -kernel your-binary.elf"
echo ""
