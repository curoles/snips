=begin rdoc
 Description::  Questa SV run script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'logger'
logger = Logger.new(STDOUT).tap do |log|
  log.progname = $module_attr[:name]
  log.level = Logger::DEBUG
end

logger.info "Run #{$module_attr[:name]}"

class ModuleRunner
  include DucCustomConfiguration

  def initialize(logger, module_attr)
    @logger = logger
    @module_attr = module_attr
    @run_dir = @module_attr[:run_dir]
    @build_dir = @module_attr[:build_dir]
    @logger.info "Run dir: #{@run_dir}"
  end

  def run
    work_dir = File.join(@build_dir, 'work')
    top_name = 'dve_opt'
    job_script = File.join(@@src_root, 'hwlib', 'questa', 'runsim.tcl')

    params =  "-64 -c -lib #{work_dir} #{top_name} -l sim.log"
    params += " -do #{job_script}"
    params += " -sva"

    env = {
      "LM_LICENSE_FILE"=>"#{@@questa[:license]}",
      #"LD_LIBRARY_PATH"=>"$LD_LIBRARY_PATH:/tools/local/xxx/lib:",
      #"HOME"=>"/dev/null"
    }

    @logger.info "Run vsim"
    vsim = @@tool[:vsim]
    #spawn(env, "#{vsim} #{params}", {:chdir=>run_dir})
    system(env, "#{vsim} #{params}", {:chdir=>@build_dir})
    return false unless ( $? == 0 )

    true
  end

end

runner = ModuleRunner.new(logger, $module_attr)
success = runner.run

logger.info(if success then 'SUCCESS' else 'FAILURE' end)

exit(1) unless success

