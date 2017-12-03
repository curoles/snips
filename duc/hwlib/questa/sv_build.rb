=begin rdoc
 Description::  Dff build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = $module_attr[:name]
  log.level = Logger::DEBUG
end

logger.info "Build #{$module_attr[:name]}"

class ModuleBuilder
  include DucCustomConfiguration

  def initialize(logger)
    @logger = logger
    @build_dir = $module_attr[:build_dir]
    @name = $module_attr[:name]
    @logger.info "Build dir: #{@build_dir}"
  end

  def run
    module_src_dir = File.join(@@src_root, 'hwlib', 'lib', @name, 'model', @@verify[:lang])
    @logger.info "Model directory: #{module_src_dir}"

    module_tb_dir = File.join(@@src_root, 'hwlib', 'lib', @name, 'test', @@verify[:vlang])
    @logger.info "TestBench directory: #{module_tb_dir}"

    compile(get_source_files(@@src_root, module_src_dir, module_tb_dir))
  end

  def compile(rtl_source_files)
    work_dir = File.join(@build_dir, 'work')
    FileUtils.remove_dir(work_dir, force:true)

    @logger.info "Run vlib"
    vlib = @@tool[:vlib]
    system("#{vlib} #{work_dir}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    #includes = "+incdir+#{@options.cosim_include} +incdir+#{smi_sim_dir}"

    #
    #  covparams = " +cover=sbceft -coverenhanced -coveropt 1 -coverfec -coverudp -covercells "
    #  covparams += " -constimmedassert -coverreportcancelled"
    #  compile_params += covparams
    #

    env = "" #"env DEFINE=..."

    source_files = rtl_source_files.join(' ')
    params =  "-64 -work #{work_dir} #{source_files}"
    params += " -l compile.log"
    params += " -mfcu -cuname pkg"

    @logger.info "Run vlog"
    vlog = @@tool[:vlog]
    system("#{env} #{vlog} #{params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )


    opt_params = "-64 -work #{work_dir} -L #{work_dir} -o dve_opt -pdu Dve +acc=a -l opt.log"

    @logger.info "Run vopt"
    vopt = @@tool[:vopt]
    system("#{vopt} #{opt_params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    true
  end

end

builder = ModuleBuilder.new(logger)
success = builder.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

