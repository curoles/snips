=begin rdoc
 Description::  Run all tests from RTL HW Library.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

#require 'optparse'
#require 'ostruct'
require 'fileutils'
#require 'pathname'
#require 'date'
#require 'find'

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = 'HWlibRun'
  log.level    = Logger::DEBUG
end

logger.level = Logger::DEBUG

logger.info 'Run RTL HW Library tests'

class HwLibRunner
  include DucCustomConfiguration

  def initialize(logger)
    @logger = logger
    @hwlib_dir = File.expand_path(File.dirname(__FILE__))
    logger.info "RTL HW Library dir: #{@hwlib_dir}"
  end

  def run
    @hwlibs = File.join(@hwlib_dir, 'lib')
    Dir.foreach(@hwlibs) do |fname|
      fpath = File.join(@hwlibs, fname)
      if File.directory?(fpath) and fname != "." and fname != ".."
        @logger.info "Scan #{File.ftype(fpath)}: #{fpath}"
        if not run_module(fname, fpath)
          @logger.error "Failed to run #{fname}"
          return false
        end
      end
    end
    true
  end

  def run_module(name, path)
    src_run_root_dir = File.join(path, 'run')
    if not File.exists?(src_run_root_dir)
      @logger.warn "#{src_run_root_dir} does not exist"
      return false
    end

    prefix = File.join(@@verify[:vlang], @@tool[:type])
    src_run_dir = File.join(src_run_root_dir, prefix)
    if not File.exists?(src_run_dir)
      @logger.warn "#{src_run_dir} does not exist"
      return false
    end

    run_script = File.join(src_run_dir, 'run.rb')
    if not File.exists?(run_script)
      @logger.warn "#{run_script} does not exist"
      return false
    end

    build_dir = File.join(@@work[:build], 'hwlib', name, prefix)
    if not File.exists?(build_dir)
      @logger.error "#{run_dir} does not exist"
      return false
    end

    run_dir = File.join(@@work[:build], 'hwlib', name, prefix)
    FileUtils::mkdir_p(run_dir)
    if not File.exists?(run_dir)
      @logger.error "#{run_dir} does not exist"
      return false
    end

    local_run_script = File.join(run_dir, 'run.rb')
    script = <<HERE
#!#{@@ruby[:path]} #{@@ruby[:options]}
# Automatically generated on #{Time.now.strftime("%d/%m/%Y %H:%M")}
require '#{@@cfg_file}'
DucCustomConfiguration.class_variable_set('@@cfg_file', '#{@@cfg_file}')
DucCustomConfiguration.class_variable_set('@@src_root', '#{@@src_root}')

$module_attr = {
  :name      => '#{name}',
  :build_dir => '#{build_dir}',
  :run_dir   => '#{run_dir}',
  :src_root  => '#{@@src_root}'
}
require '#{run_script}'
HERE

    File.open(local_run_script, "w") do |f|
      f << script
      f.chmod(0777)
    end

    system("#{local_run_script}", {:chdir=>run_dir})
    return false unless ( $? == 0 )

    true
  end

end #class HwLibRunner

logger.info 'Create runner'
runner = HwLibRunner.new(logger)

logger.info 'Run'
success = runner.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success
