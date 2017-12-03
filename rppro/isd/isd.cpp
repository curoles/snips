#include "format.h"
#include "instruction.h"

#include "logging.h"

Log& get_logger()
{
    static Log logger_instance;
    static bool initialized = false;

    if (not initialized)
    {
        initialized = true;
        logger_instance.add_stdout_stream();
        logger_instance.add_stream("isd.log");
    }

    return logger_instance;
}

int main()
{
    Log& log = get_logger();

    log << "Instruction Set Designer\n";

    format::Formats formats;

    formats.read("../../rppro/isd/arch/PDP-11/format.xml");
    formats.output("formats.html");

    Insns insns(formats);
    insns.read_insn_dir("../../rppro/isd/arch/PDP-11/insn");
    insns.output();

    return 0;
}
