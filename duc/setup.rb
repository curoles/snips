#!/usr/bin/ruby -W1

=begin rdoc
 Description::  Setup and configure DUC tool.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'optparse'
require 'ostruct'
require 'fileutils'
require 'pathname'
require 'date'
#require 'find'

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = 'Setup'
  log.level    = Logger::DEBUG
end

options = OpenStruct.new

OptionParser.new do |opts|

  opts.banner = "Usage: setup.rb --config <your_configuration_file.rb>"
  opts.separator ""

  opts.on("--config PATH", "Configuration file") do |cfg_file_path|
    if Pathname(cfg_file_path).absolute?
      require cfg_file_path
    else
      require_relative cfg_file_path
    end
    options.cfg_file = Pathname(cfg_file_path).realpath
  end

  opts.on_tail("--version", "Show version") do
    puts "0.1"
    exit
  end

  #http://en.wikipedia.org/wiki/Command-line_interface#Built-in_usage_help
  opts.on_tail("-h", "--help", "Print help") do
    puts opts.help()
    exit 1
  end

end.parse!

unless options.cfg_file
  puts "Please provide configuration file, use --help to see usage"
  exit 1
end

logger.info 'Setup DUC tool'

logger.info 'Build configurator'
class Configurator
  include DucCustomConfiguration

  def initialize(logger, options)
    @logger = logger
    @options = options
    @duc_root = File.expand_path(File.dirname(__FILE__))
    @logger.info "DUC path to source: #{@duc_root}"
  end

  def run
    make_directories
    make_hwlib_build_script
    make_hwlib_run_script
    make_projects
    true
  end

  def make_directories
    @logger.info "Make work directory: #{@@work[:base]}"
    FileUtils::mkdir_p @@work[:base]
    @logger.info "Make build directory: #{@@work[:build]}"
    FileUtils::mkdir_p @@work[:build]
    FileUtils::mkdir_p File.join(@@work[:build], 'hwlib')
    #@logger.info "Make run directory: #{@@work[:run]}"
    #FileUtils::mkdir_p @@work[:run]
  end

  def make_hwlib_build_script
    dir = File.join(@@work[:build], 'hwlib')
    script_file = "#{dir}/build.rb"

    script = <<HERE
#!#{@@ruby[:path]} #{@@ruby[:options]}
# Automatically generated on #{Time.now.strftime("%d/%m/%Y %H:%M")}
require '#{@options.cfg_file}'
DucCustomConfiguration.class_variable_set('@@cfg_file', '#{@options.cfg_file}')
DucCustomConfiguration.class_variable_set('@@src_root', '#{@duc_root}')
require '#{@duc_root}/hwlib/build'
HERE

    File.open(script_file, "w") do |f|
      f << script
      f.chmod(0777)
    end

  end

  def make_hwlib_run_script
    dir = File.join(@@work[:build], 'hwlib')
    script_file = File.join(dir, 'run.rb')

    script = <<HERE
#!#{@@ruby[:path]} #{@@ruby[:options]}
# Automatically generated on #{Time.now.strftime("%d/%m/%Y %H:%M")}
require '#{@options.cfg_file}'
DucCustomConfiguration.class_variable_set('@@cfg_file', '#{@options.cfg_file}')
DucCustomConfiguration.class_variable_set('@@src_root', '#{@duc_root}')
require '#{@duc_root}/hwlib/run'
HERE

    File.open(script_file, "w") do |f|
      f << script
      f.chmod(0777)
    end

  end

  def make_projects
    make_project('mig1')
    make_project('v200')
  end

  def make_prj_script(path, type)
    dir = File.join(@@work[:build], 'prj', path)

    script = <<HERE
#!#{@@ruby[:path]} #{@@ruby[:options]}
# Automatically generated on #{Time.now.strftime("%d/%m/%Y %H:%M")}
require '#{@options.cfg_file}'
DucCustomConfiguration.class_variable_set('@@cfg_file', '#{@options.cfg_file}')
DucCustomConfiguration.class_variable_set('@@src_root', '#{@duc_root}')

$prj_attr = {
  :name      => '#{path}',
  :build_dir => '#{dir}'
}

require '#{@duc_root}/prj/#{path}/#{type}'
HERE

    script_file = File.join(dir, type+'.rb')
    @logger.info("Creating #{script_file}")

    File.open(script_file, "w") do |f|
      f << script
      f.chmod(0777)
    end

  end

  def make_project(prj_name)
    FileUtils::mkdir_p File.join(@@work[:build], 'prj', prj_name)
    make_prj_script(prj_name, 'build')
    make_prj_script(prj_name, 'run')
  end

end #class Configurator

logger.info 'Create configurator'
configurator = Configurator.new(logger, options)

logger.info 'Run configurator'
success = configurator.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit 1 unless success
#otherwise we exit with 0 by default
