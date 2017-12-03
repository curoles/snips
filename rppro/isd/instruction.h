/**@file
 * @brief     Instruction
 * @author    2013 Igor Lesik
 * @copyright 2013 Igor Lesik
 *
 */
#pragma once

#include <string>
#include <list>

#include "logging.h"
#include "format.h"

class Insn
{
private:
    std::string mn;
    std::string name;

    std::string format_id;
    const format::Format* format;

    Log& log;

public:
    Insn(const std::string& mn="", const std::string& name=""):
        mn(mn), name(name),
        format_id("?"), format(nullptr), log(get_logger())
    {
    }

    bool set_format(const std::string& format, const format::FrmtList& formats);
    bool set_field(const std::string& field_name, const std::string& val_str);

    friend class Insns;
};

class Insns
{
public:
    typedef std::list<Insn> InsnList;

private:
    InsnList m_insns;

    const format::Formats& m_formats;

    Log& log;

public:
    Insns(const Insns&) = delete;

    Insns(const format::Formats& formats):m_formats(formats),
        log(get_logger())
    {}

    void read_insn_file(const std::string& file_name);
    void read_insn_dir(const std::string& dir_name);

    void output();
    void output_insn(const Insn& insn);

};
