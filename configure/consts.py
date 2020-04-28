# See LICENSE.incore for license details

length_check_fields=['reset_pc', 'physical_addr_size']

bsc_cmd = '''bsc -u -verilog -elab -vdir {0} -bdir {1} -info-dir {1} \
+RTS -K40000M -RTS -check-assert  -keep-fires \
-opt-undetermined-vals -remove-false-rules -remove-empty-rules \
-remove-starved-rules -remove-dollar -unspecified-to X -show-schedule \
-show-module-use {2}'''

verilator_cmd = ''' -O3 -LDFLAGS "-static" --x-assign fast \
 --x-initial fast --noassert sim_main.cpp --bbox-sys -Wno-STMTDLY \
 -Wno-UNOPTFLAT -Wno-WIDTH -Wno-lint -Wno-COMBDLY -Wno-INITIALDLY \
 --autoflush {0} {1} --threads {2} -DBSV_RESET_FIFO_HEAD \
 -DBSV_RESET_FIFO_ARRAY --output-split 20000 \
 --output-split-ctrace 10000'''

makefile_temp='''
VERILOGDIR:={0}

BSVBUILDDIR:={1}

BSVOUTDIR:={2}

BSCCMD:={3}

BSVINCDIR:=.:%/Libraries{4}

TOP_MODULE:={5}

TOP_DIR:={6}

TOP_FILE:={7}

VERILATOR_FLAGS:={8}

VERILATOR_SPEED:={9}

BS_VERILOG_LIB:={10}/../lib/Verilog/

SHAKTI_HOME:={11}

XLEN:={12}
'''

dependency_yaml='''
caches_mmu:
  repo: https://gitlab.com/shaktiproject/uncore/caches_mmu
  checkout: 8.2.0
  commitid:   
  patch:
common_bsv:
  repo: https://gitlab.com/shaktiproject/common_bsv
  checkout: master
  commitid:
  patch:
devices:
  repo: https://gitlab.com/shaktiproject/uncore/devices
  checkout: 5.0.1
  commitid:
  patch:
fabrics:
  repo: https://gitlab.com/shaktiproject/uncore/fabrics
  checkout: 1.2.0
  commitid:
  patch:
common_verilog:
  repo: https://gitlab.com/shaktiproject/common_verilog
  checkout: master
  commitid:
  patch:
verification:
  repo: https://gitlab.com/shaktiproject/verification_environment/verification
  checkout: 4.0.0
  commitid:
  patch:
    - [riscv-tests/env , verification/patches/riscv-tests-shakti-signature.patch]
benchmarks:
  repo: https://gitlab.com/shaktiproject/cores/benchmarks
  checkout: master
  commitid:
  patch:
'''
prelude = [
    'Connectable',
    'FIFOF',
    'BUtils',
    'GetPut',
    'FIFO',
    'SpecialFIFOs',
    'Clocks',
    'DReg',
    'FIFOLevel',
    'Vector',
    'Counter',
    'ConfigReg',
    'Assert',
    'BRAMCore',
    'BRAM',
    'RegFile',
    'UniqueWrappers',
    'LFSR',
    'Randomizable',
    'StmtFSM',
    'List',
    'ClientServer',
    'Probe',
    'OVLAssertions',
    'CBus',
    'ModuleCollect',
    'RevertReg',
    'MIMO',
    'List',
    'OInt',
    'Memory',
    'Cntrs',
    'GrayCounter',
    'CompletionBuffer',
    'DefaultValue',
    'TieOff',
    'ZBus',
    'CRC',
    'Real',
    'Gearbox',
    'AlignedFIFOs'
]

