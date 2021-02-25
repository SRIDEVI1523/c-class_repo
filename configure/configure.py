
from cerberus import Validator
from configure.utils import yaml
import configure.utils as utils
from configure.errors import ValidationError
from configure.consts import *
import os
import logging
import sys
import math
from repomanager.rpm import repoman
from riscv_config.warl import warl_interpreter

logger = logging.getLogger(__name__)

bsc_path = utils.which("bsc")[:-7]

bsv_path_file = open('bsvpath','r').read().splitlines()

def check_prerequisites():
    utils.which('bsc')
    utils.which('bluetcl')
    utils.which('csrbox')
    utils.which('riscv-config')

def handle_dependencies(verbose,clean,update,patch):
    repoman(dependency_yaml,clean,update,patch,False,'./')

def specific_checks(foo):

    logger.info('Performing Specific Checks')

    xlen = 64
    max_value = 2 ** 64
    if '32' in foo['ISA']:
        max_value = 2 ** 32
        xlen = 32

    # check if default values are correctly assigned
    for field in length_check_fields:
        if foo[field] > (max_value-1):
            logger.error('Default Value of ' + field + ' exceeds the max\
 allowed value')
            sys.exit(1)

    # check s_extension
#    s_mode = foo['s_extension']['mode']
#    s_itlbsize = foo['s_extension']['itlb_size']
#    s_dtlbsize = foo['s_extension']['dtlb_size']
#    s_asid_width = foo['s_extension']['asid_width']
#    if 'S' in foo['ISA']:
#        if xlen is 32 and s_mode != 'sv32' :
#            logger.error('Only sv32 supported in RV32')
#            sys.exit(1)
#        if xlen is 64 and s_mode not in ['sv48', 'sv39'] :
#            logger.error('Only sv39/sv48 supported in RV64')
#            sys.exit(1)
#        if xlen is 32 and s_asid_width > 9:
#            logger.error('in RV32 ASID cannot be greater than 9')
#            sys.exit(1)
#        if xlen is 64 and s_asid_width > 16:
#            logger.error('in RV32 ASID cannot be greater than 16')
#            sys.exit(1)

    # check m_extension

    m_mulstages = foo['m_extension']['mul_stages']
    m_divstages = foo['m_extension']['div_stages']
    if 'M' in foo['ISA']:
        if m_mulstages > xlen:
            logger.error('Multiplication stages cannot exceed XLEN')
            sys.exit(1)
        if m_divstages > xlen:
            logger.error('Division stages cannot exceed XLEN')
            sys.exit(1)

    # check icache
    icache_enable = foo['icache_configuration']['instantiate']
    i_words = foo['icache_configuration']['word_size']
    i_blocks = foo['icache_configuration']['block_size']
    i_sets = foo['icache_configuration']['sets']
    i_ways = foo['icache_configuration']['ways']
    if icache_enable and 'S' in foo['ISA']:
        if i_words*i_sets*i_blocks > 4096:
            logger.error('Since Supervisor is enabled, each way of I-Cache\
 should be less than 4096 Bytes')
            sys.exit(1)
    
    # check dcache
    dcache_enable = foo['dcache_configuration']['instantiate']
    d_words = foo['dcache_configuration']['word_size']
    d_blocks = foo['dcache_configuration']['block_size']
    d_sets = foo['dcache_configuration']['sets']
    d_ways = foo['dcache_configuration']['ways']
    if dcache_enable:
      if xlen != (d_words * 8):
        logger.error('D_WORDS for a '+str(xlen)+'-bit core should be '+
          str(xlen/8))
    if dcache_enable and 'S' in foo['ISA']:
        if i_words*i_sets*i_blocks > 4096:
            logger.error('Since Supervisor is enabled, each way of D-Cache\
 should be less than 4096 Bytes')
            sys.exit(1)
        if d_words * 8 != xlen:
            logger.error('D-Cache d_words should be ' + str(xlen/8))
            sys.exit(1)

def capture_compile_cmd(foo, isa_node, debug_spec):
    global bsc_cmd
    global bsc_defines

    logger.info('Generating BSC compile options')
    xlen = 64
    if '32' in isa_node['ISA']:
        xlen = 32

    if 'S' in isa_node['ISA']:
        s_itlbsize = foo['s_extension']['itlb_size']
        s_dtlbsize = foo['s_extension']['dtlb_size']
        satp_modewarl =\
                (warl_interpreter(isa_node['satp']['rv'+str(xlen)]['mode']['type']['warl']))
        if satp_modewarl.islegal(9,[]):
            s_mode = 'sv48'
        elif satp_modewarl.islegal(8,[]):
            s_mode = 'sv39'
        elif satp_modewarl.isa_node(1,[]):
            s_mode = 'sv32'
        else:
            logger.error('Cannot deduce supervisor mode from satp.mode')
            raise SystemExit

        asidlen = 0
        asid_mask = 0xFFFF
        satp_asidwarl =\
                (warl_interpreter(isa_node['satp']['rv'+str(xlen)]['asid']['type']['warl']))
        while asid_mask != 0:
            if satp_asidwarl.islegal(int(asid_mask),[]):
                asidlen = int(math.log2(asid_mask+1))
                break
            else:
                asid_mask = asid_mask >> 1

    m_mulstages = foo['m_extension']['mul_stages']
    m_divstages = foo['m_extension']['div_stages']
    mhpm_eventcount = foo['total_events']
    suppress = ''

    test_memory_size = foo['bsc_compile_options']['test_memory_size']
    test_memory_size = math.log2(test_memory_size)
    macros = 'Addr_space='+str(int(test_memory_size))
    if "all" in foo['bsc_compile_options']['suppress_warnings']:
        suppress += ' -suppress-warnings\
 G0010:T0054:G0020:G0024:G0023:G0096:G0036:G0117:G0015'
    elif "none" not in foo['bsc_compile_options']['suppress_warnings']:
        suppress += ' -suppress-warnings '
        for w in foo['bsc_compile_options']['suppress_warnings']:
            suppress += str(w)+':'
        suppress = suppress[:-1]
    if debug_spec is not None:
        macros += ' debug'

    if foo['bsc_compile_options']['assertions']:
        macros += ' ASSERT'
    if foo['bsc_compile_options']['trace_dump']:
        macros += ' rtldump'

    macros += ' RV'+str(xlen)+' ibuswidth='+str(xlen)
    macros += ' dbuswidth='+str(xlen)
    macros += ' resetpc='+str(foo['reset_pc'])
    macros += ' paddr='+str(isa_node['physical_addr_sz'])
    macros += ' vaddr='+str(xlen)
    macros += ' causesize=6'
    macros += ' CORE_'+str(foo['bus_protocol'])
    macros += ' iesize='+str(foo['iepoch_size'])
    macros += ' desize='+str(foo['depoch_size'])
    macros += ' dtvec_base='+str(foo['dtvec_base'])

    if foo['bsc_compile_options']['compile_target'] == 'sim':
        macros += ' simulate'
    if foo['bsc_compile_options']['open_ocd']:
        macros += ' openocd'

    macros += ' mhpm_eventcount=' + str(mhpm_eventcount)
    
    if 'A' in foo['ISA']:
        macros += ' atomic'
    if 'F' in foo['ISA']:
        macros += ' spfpu'
    if 'D' in foo['ISA']:
        macros += ' dpfpu'
    if 'C' in foo['ISA']:
        macros += ' compressed'
    if 'M' in foo['ISA']:
        macros += ' muldiv'
        macros += ' MULSTAGES='+str(m_mulstages)
        macros += ' DIVSTAGES='+str(m_divstages)
    if 'U' in foo['ISA']:
        macros += ' user'
    if 'N' in foo['ISA']:
        macros += ' usertraps'
    if 'S' in foo['ISA']:
        macros += ' supervisor'
        macros += ' itlbsize='+str(s_itlbsize)
        macros += ' dtlbsize='+str(s_dtlbsize)
        macros += ' asidwidth='+str(asidlen)
        macros += ' ' + s_mode
    if foo['branch_predictor']['instantiate']:
        macros += ' bpu'
        macros += ' '+foo['branch_predictor']['predictor']
        macros += ' btbdepth='+str(foo['branch_predictor']['btb_depth'])
        macros += ' bhtdepth='+str(foo['branch_predictor']['bht_depth'])
        macros += ' histlen='+str(foo['branch_predictor']['history_len'])
        macros += ' histbits='+str(foo['branch_predictor']['history_bits'])
        macros += ' rasdepth='+str(foo['branch_predictor']['ras_depth'])
        if 'enable' in foo['branch_predictor']['on_reset']:
            macros += ' bpureset=1'
        else:
            macros += ' bpureset=0'
        if foo['branch_predictor']['ras_depth'] > 0:
            macros += ' bpu_ras'

    macros += ' iwords='+str(foo['icache_configuration']['word_size'])
    macros += ' iblocks='+str(foo['icache_configuration']['block_size'])
    macros += ' iways='+str(foo['icache_configuration']['ways'])
    macros += ' isets='+str(foo['icache_configuration']['sets'])
    macros += ' ifbsize='+str(foo['icache_configuration']['fb_size'])
    if foo['icache_configuration']['one_hot_select']:
        macros += ' icache_onehot=1'
    else:
        macros += ' icache_onehot=0'
    if( foo['icache_configuration']['ecc_enable']):
        macros += ' icache_ecc'
    if foo['icache_configuration']['instantiate']:
        macros += ' icache'
        if foo['icache_configuration']['on_reset']:
            macros += ' icachereset=1'
        else:
            macros += ' icachereset=0'
    if foo['icache_configuration']['instantiate'] or \
            foo['branch_predictor']['instantiate']:
        macros += ' ifence'
    if foo['icache_configuration']['replacement'] == "RANDOM":
        macros += ' irepl=0'
    if foo['icache_configuration']['replacement'] == "RR":
        macros += ' irepl=1'
    if foo['icache_configuration']['replacement'] == "PLRU":
        macros += ' irepl=2'
    
    macros += ' dwords='+str(foo['dcache_configuration']['word_size'])
    macros += ' dblocks='+str(foo['dcache_configuration']['block_size'])
    macros += ' dways='+str(foo['dcache_configuration']['ways'])
    macros += ' dsets='+str(foo['dcache_configuration']['sets'])
    macros += ' dfbsize='+str(foo['dcache_configuration']['fb_size'])
    macros += ' dsbsize='+str(foo['dcache_configuration']['sb_size'])
    if foo['dcache_configuration']['rwports'] == 2:
        macros += ' dcache_dualport'
    if foo['dcache_configuration']['one_hot_select']:
        macros += ' dcache_onehot=1'
    else:
        macros += ' dcache_onehot=0'
    if( foo['dcache_configuration']['ecc_enable']):
        macros += ' dcache_ecc'
    if foo['dcache_configuration']['instantiate']:
        macros += ' dcache'
        if foo['dcache_configuration']['on_reset']:
            macros += ' dcachereset=1'
        else:
            macros += ' dcachereset=0'
    if foo['dcache_configuration']['replacement'] == "RANDOM":
        macros += ' drepl=0'
    if foo['dcache_configuration']['replacement'] == "RR":
        macros += ' drepl=1'
    if foo['dcache_configuration']['replacement'] == "PLRU":
        macros += ' drepl=2'

    if foo['fpu_trap']:
        macros += ' arith_trap'

    macros += ' csr_low_latency'
    
    total_counters = 0
    pmp_entries = 0
    for node in isa_node:
        if 'mhpmcounter' in node:
            if isa_node[node]['rv'+str(xlen)]['accessible']:
                total_counters += 1
        if 'pmpaddr' in node:
            if isa_node[node]['rv'+str(xlen)]['accessible']:
                pmp_entries += 1

    if total_counters > 0:
        macros += ' perfmonitors'
    if pmp_entries > 0:
        macros += ' pmp'
        macros += ' pmpentries='+str(pmp_entries)
        macros += ' pmp_grainbits='+str(isa_node['pmp_granularity']+2)


    if foo['no_of_triggers'] > 0:
        macros += ' triggers  trigger_num='+str(foo['no_of_triggers'])
        macros += ' mcontext=0  scontext=0'
        

    bsc_cmd = bsc_cmd.format(foo['bsc_compile_options']['verilog_dir'],
            foo['bsc_compile_options']['build_dir'], suppress)
    bsc_defines = macros

def generate_makefile(foo, logging=False):
    global bsc_cmd
    global verilator_cmd
    global bsc_defines
    
    cwd = os.getcwd()
    make_file = open('makefile.inc','w')
    xlen = 64
    if '32' in foo['ISA']:
        xlen = 32
    top_file = foo['bsc_compile_options']['top_file']
    top_module = foo['bsc_compile_options']['top_module']
    top_dir = foo['bsc_compile_options']['top_dir']
    verilog_dir = foo['bsc_compile_options']['verilog_dir']
    bsv_build_dir = foo['bsc_compile_options']['build_dir']
    verilator_threads = foo['verilator_configuration']['threads']

    if foo['verilator_configuration']['trace']:
        verilator_trace = '--trace'
    else:
        verilator_trace = ''
    if "none" in foo['verilator_configuration']['coverage']:
        verilator_coverage = ''
    elif "all" in foo['verilator_configuration']['coverage']:
        verilator_coverage = '--coverage'
    else:
        verilator_coverage = '--coverage-'+\
                foo['verilator_configuration']['coverage']
    if "fast" in foo['verilator_configuration']['sim_speed']:
        verilator_speed = 'OPT_SLOW="-O3" OPT_FAST="-O3"'
    else:
        verilator_speed = ''
    verilator_cmd = verilator_cmd.format(verilator_trace, verilator_coverage,
            verilator_threads)
    path = '.:%/Libraries'
    for p in bsv_path_file:
        path += ':'+p
    curr_dir = os.getcwd()
    make_file.write(makefile_temp.format(verilog_dir, bsv_build_dir, 
        "bin", bsc_cmd,bsc_defines,path, bsc_path, top_module, top_dir, top_file, verilator_cmd, 
        verilator_speed, curr_dir, xlen, top_file[:-3]+'bo'))
    if logging:
        logger.info(str(make_file.name)+' generated')

    if logging:
        logger.info('Creating Dependency graph')

    depends = ' BSC_PATH="{0}" BSC_DEFINES="{1}" BSC_BUILDDIR="{2}" \
 BSC_TOPFILE="{3}" OUTPUTFILE=depends.mk ./genDependencies.tcl'.format(\
 path, bsc_defines, bsv_build_dir, top_dir+'/'+top_file)

    os.makedirs(verilog_dir, exist_ok=True)
    os.makedirs(bsv_build_dir, exist_ok=True)
    utils.shellCommand(depends).run(cwd=cwd)
    dependency = open('depends.mk','r').read()
    dependency = dependency.replace('$(BLUESPECDIR)',bsc_path+'/lib')
    newdependency = open('depends.mk','w').write(dependency)
    if logging:
        logger.info('Dependency Graph Created')
    
def validate_specs(core_spec, isa_spec, debug_spec, logging=False):

    schema = 'configure/schema.yaml'
    # Load input YAML file
    if logging:
        logger.info('Loading core file: ' + str(core_spec))
    inp_yaml = utils.load_yaml(core_spec)
    if logging:
        logger.info('Loading isa file: ' + str(isa_spec))
    isa_yaml = utils.load_yaml(isa_spec)
    
    isa_string = isa_yaml['hart0']['ISA']
    if 64 in isa_yaml['hart0']['supported_xlen']:
        xlen = 64
        mabi = 'lp64'
        march = 'rv64i'
    else:
        xlen = 32
        mabi = 'ilp32'
        march = 'rv32i'

    if 'M' in isa_string:
        march += 'm'
    if 'C' in isa_string:
        march += 'c'
    if 'F' in isa_string:
        march += 'F'
    if 'D' in isa_string:
        march += 'D'


    inp_yaml['ISA'] = isa_yaml['hart0']['ISA']
    # instantiate validator
    if logging:
        logger.info('Load Schema ' + str(schema))
    schema_yaml = utils.load_yaml(schema)

    validator = Validator(schema_yaml)
    normalized = validator.normalized(inp_yaml, schema_yaml)

    # Perform Validation
    if logging:
        logger.info('Initiating Validation')
    valid = validator.validate(normalized)

    # Print out errors
    if valid:
        if logging:
            logger.info('No Syntax errors in Input Yaml.')
    else:
        error_list = validator.errors
        raise ValidationError("Error in " + core_spec + ".", error_list)
    specific_checks(normalized)
    capture_compile_cmd(normalized, isa_yaml['hart0'], debug_spec)
    generate_makefile(normalized, logging)

    logger.info('Configuring Boot-Code')
    ofile = open('boot/Makefile.inc','w')
    ofile.write('XLEN='+str(xlen))
    ofile.close()

    logger.info('Configuring the Benchmarks')
    ofile = open('benchmarks/Makefile.inc','w')
    ofile.write('xlen=' + str(xlen) + '\n')
    ofile.write('march=' + march + '\n')
    ofile.write('mabi=' + mabi + '\n')
    ofile.close()

    cwd = os.getcwd()
    if logging:
        logger.info('Cleaning previously built code')
    utils.shellCommand('make clean').run(cwd=cwd)
    if logging:
        logger.info('Run make -j<jobs>')
