=begin rdoc
 Description::  Dff Verilator run script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = 'Run Dff'
  log.level    = Logger::DEBUG
end

logger.info 'Run Dff'

class ModuleRunner
  include DucCustomConfiguration

  def initialize(logger)
    @logger = logger
    @run_dir = @@run_dir
    @logger.info "Run dir: #{@run_dir}"
  end

  def run
    executable = File.join(@run_dir, 'obj_dir', 'VDve')
    @logger.info "Run #{executable}"
    system("#{executable}", {:chdir=>@run_dir})
    return false unless ( $? == 0 )

    true
  end

end

runner = ModuleRunner.new(logger)
success = runner.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

