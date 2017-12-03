=begin rdoc
 Description::  Verilator build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end


require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = $module_attr[:name]
  log.level    = Logger::DEBUG
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

  #
  # http://www.veripool.org/projects/verilator/wiki/Manual-verilator
  #
  def compile(rtl_source_files)
    src_files = rtl_source_files.join(' -cc ')

    tb_main = File.join(@@src_root, 'hwlib', 'verilator', 'main.cpp')

    params = " -Wall -cc #{src_files} --exe #{tb_main} "
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

end

builder = ModuleBuilder.new(logger)
success = builder.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

