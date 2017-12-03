=begin rdoc
 Description::  Build RTL HW Library.
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
  log.progname = 'HWlibBuild'
  log.level    = Logger::DEBUG
end

logger.info 'Build RTL HW Library'

class HwLibBuilder
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
        if not build_module(fname, fpath)
          @logger.error "Failed to build #{fname}"
          return false
        end
      end
    end
    true
  end

  def build_module(name, path)
    src_build_root_dir = File.join(path, 'build')
    if not File.exist?(src_build_root_dir)
      @logger.warn "#{src_build_root_dir} does not exist"
      return false
    end

    prefix = File.join(@@verify[:vlang], @@tool[:type])
    src_build_dir = File.join(src_build_root_dir, prefix)
    if not File.exist?(src_build_dir)
      @logger.warn "#{src_build_dir} does not exist"
      return false
    end

    build_script = File.join(src_build_dir, 'build.rb')
    if not File.exist?(build_script)
      @logger.warn "#{build_script} does not exist"
      return false
    end

    build_dir = File.join(@@work[:build], 'hwlib', name, prefix)
    FileUtils::mkdir_p(build_dir)
    if not File.exist?(build_dir)
      @logger.error "#{build_dir} does not exist"
      return false
    end

    local_build_script = File.join(build_dir, 'build.rb')
    script = <<HERE
#!#{@@ruby[:path]} #{@@ruby[:options]}
# Automatically generated on #{Time.now.strftime("%d/%m/%Y %H:%M")}
require '#{@@cfg_file}'
DucCustomConfiguration.class_variable_set('@@cfg_file', '#{@@cfg_file}')
DucCustomConfiguration.class_variable_set('@@src_root', '#{@@src_root}')

$module_attr = {
  :name      => '#{name}',
  :build_dir => '#{build_dir}',
  :src_root  => '#{@@src_root}'
}

require '#{build_script}'
HERE

    File.open(local_build_script, "w") do |f|
      f << script
      f.chmod(0777)
    end

    system("#{local_build_script}", {:chdir=>build_dir})
    return false unless ( $? == 0 )

    true
  end

end #class HwLibBuilder

logger.info 'Create builder'
builder = HwLibBuilder.new(logger)

logger.info 'Run builder'
success = builder.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success
#otherwise we exit with 0 by default
