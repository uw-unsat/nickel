## Project configuration

# CPU architecture (only x86_64 supported for now)
ARCH            := x86_64

# Output directory
O               := o.$(ARCH)

# VMM/guest configuration
VMM             := $(O)/monitor.bin
KERNEL          := $(O)/nistar.bin
APPEND          :=
INITRD          := $(O)/nistar/user/initrd.cpio

# Number of CPUs used in simulation
NR_CPUS         := 1

# configuration used by Bochs for simulation
BOCHS           := bochs
BOCHS_CPU       := broadwell_ult

# configuration used by QEMU for simulation
# pmu=off: workaround for QEMU/KVM crash when running in VMware
# https://bugs.launchpad.net/qemu/+bug/1661386
QEMU            := qemu-system-$(ARCH)
QEMU_ACCEL      := kvm:hvf:tcg
QEMU_CPU        := max,pmu=off
QEMU_IOMMU      := intel-iommu
QEMU_NIC        := e1000
QEMU_USE_VIRTIO := 0

# Use ccache for faster build times
USE_CCACHE      := 0

GIT_CLEAN       := 0

# Force clang as compiler (default 1 on macOS, 0 on linux)
# USE_CLANG     := 1

# Override tool prefix
# TOOLPREFIX    := $(ARCH)-linux-gnu-

# suppress "Entering directory" and "Leaving directory" messages
MAKEFLAGS       += --no-print-directory

# Default IPXE host and port
IPXE_CHAINLOADER_HOST := lukes-macbook-pro.dyn.cs.washington.edu
IPXE_HOST             := lukes-macbook-pro.dyn.cs.washington.edu
IPXE_PORT             := 8081

# overwrite using local settings
-include        local.mk
