=begin rdoc
 Description::  Build Mig1 project.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = 'Mig1'
  log.level    = Logger::DEBUG
end

logger.info 'Build Mig1'

class Mig1Builder
  include DucCustomConfiguration

  def initialize(logger)
    @logger = logger
    @build_dir = $prj_attr[:build_dir]
    @prj_dir = File.expand_path(File.dirname(__FILE__))
    logger.info "Mig1 project dir: #{@prj_dir}"
    logger.info "Mig1 build dir: #{@build_dir}"
  end

  def run
    @logger.info "Tool type: #{@@tool[:type]}"
    case @@tool[:type]
    when "verilator"
      return build_with_verilator
    when "questa"
      return build_with_questa
    else
      return false
    end
    false
  end

  def get_source_files(src_root, prj_src)
    [ File.join(prj_src,  'rtl', 'Mig1.v'),
      File.join(prj_src,  'rtl', 'ProgramCounter.v'),
      File.join(prj_src,  'rtl', 'FrontEnd.v'),
      File.join(prj_src,  'rtl', 'Decoder.v'),
      File.join(prj_src,  'rtl', 'RegisterFile.v'),
      File.join(prj_src,  'rtl', 'Executor.v'),
      File.join(src_root, 'hwlib', 'lib', 'VRom', 'model', 'v', 'VRom.v')
    ]
  end

  #
  # http://www.veripool.org/projects/verilator/wiki/Manual-verilator
  #
  def build_with_verilator
    design_files = get_source_files(@@src_root, @prj_dir)
    tb_files = [
      File.join(@prj_dir, 'rtl', 'Dve.v')
    ]

    srcs = tb_files + design_files

    src_files = srcs.join(' -cc ')

    tb_main = File.join(@@src_root, 'hwlib', 'verilator', 'main.cpp')

    params = " -Wall -cc #{src_files} --exe #{tb_main} "
    params += " --top-module Dve "
    params += " --assert "

    @logger.info "Run verilator"
    vlog = @@tool[:vlog]
    system("#{vlog} #{params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    obj_dir = File.join(@build_dir, 'obj_dir')
    system("make -f VDve.mk VDve", {:chdir=>obj_dir})
    return false unless ( $? == 0 )

    true
  end

  def build_with_questa
    design_files = get_source_files(@@src_root, @prj_dir)
    tb_files = [
      File.join(@prj_dir, 'rtl', 'Dve.sv'),
      File.join(@@src_root, 'hwlib', 'sv', 'SimClkGen.sv'),
      File.join(@@src_root, 'hwlib', 'sv', 'SimRstGen.sv')
    ]

    srcs = tb_files + design_files

    work_dir = File.join(@build_dir, 'work')
    FileUtils.remove_dir(work_dir, force:true)

    @logger.info "Run vlib"
    vlib = @@tool[:vlib]
    system("#{vlib} #{work_dir}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    params =  "-64 -work #{work_dir} "
    params += srcs.join(' ')
    params += " -l compile.log"
    params += " -mfcu -cuname pkg"

    @logger.info "Run vlog"
    vlog = @@tool[:vlog]
    env = ""
    system("#{env} #{vlog} #{params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )


    opt_params = "-64 -work #{work_dir} -L #{work_dir} "
    opt_params += " -o dve_opt -pdu Dve +acc=a -l opt.log"

    @logger.info "Run vopt"
    vopt = @@tool[:vopt]
    system("#{vopt} #{opt_params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    true
  end

end #class Mig1Builder

logger.info 'Create Mig1 builder'
builder = Mig1Builder.new(logger)

logger.info 'Run Mig1 builder'
success = builder.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

