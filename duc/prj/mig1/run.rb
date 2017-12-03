=begin rdoc
 Description::  Run Mig1 simulation.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = 'Mig1'
  log.level    = Logger::DEBUG
end

logger.info 'Run Mig1'

class Mig1Runner
  include DucCustomConfiguration

  def initialize(logger)
    @logger = logger
    @build_dir = $prj_attr[:build_dir]
    @prj_dir = File.expand_path(File.dirname(__FILE__))
    logger.info "Mig1 project dir: #{@prj_dir}"
    logger.info "Mig1 build dir: #{@build_dir}"
    @run_dir = File.join(@build_dir, 'run')
    FileUtils.mkdir_p(@run_dir)
    logger.info "Mig1 run dir: #{@run_dir}"
  end

  def run
    load_program_to_ROM
    @logger.info "Tool type: #{@@tool[:type]}"
    case @@tool[:type]
    when "verilator"
      return run_verilator_build
    when "questa"
      return run_questa_build
    else
      return false
    end
    false
  end

  def load_program_to_ROM
    mem_file = File.join(@run_dir, 'memory.txt')
    macode = <<HERE
00000000000000000000000000000001
00000000000000000000000000000010
00000000000000000000000000000011
00000000000000000000000000000100
00000000000000000000000000000101
00000000000000000000000000000110
00000000000000000000000000000111
00000000000000000000000000001000
00000000000000000000000000001001
00000000000000000000000000001010
HERE

    File.open(mem_file, "w") do |f|
      f << macode
    end

  end

  def run_verilator_build
    executable = File.join(@build_dir, 'obj_dir', 'VDve')
    @logger.info "Run #{executable}"
    system("#{executable}", {:chdir=>@run_dir})
    return false unless ( $? == 0 )

    true
  end

  def run_questa_build
    work_dir = File.join(@build_dir, 'work')
    top_name = 'dve_opt'
    job_script = File.join(@@src_root, 'hwlib', 'questa', 'runsim.tcl')

    params =  "-64 -c -lib #{work_dir} #{top_name} -l sim.log"
    params += " -do #{job_script}"
    params += " -sva"

    env = {
      "LM_LICENSE_FILE"=>"#{@@questa[:license]}",
    }

    @logger.info "Run vsim"
    vsim = @@tool[:vsim]
    system(env, "#{vsim} #{params}", {:chdir=>@run_dir})
    return false unless ( $? == 0 )

    true
  end

end #class Mig1Runner

logger.info 'Create Mig1 runner'
runner = Mig1Runner.new(logger)

logger.info 'Start Mig1 runner'
success = runner.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

