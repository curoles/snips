/**@file
 * @brief     Instruction
 * @author    2013 Igor Lesik
 * @copyright 2013 Igor Lesik
 *
 */
#include "instruction.h"

#include <iostream>
#include <regex>

#include "cgem/Dir.h"
#include "cgem/File.h"
#include "cgem/XMLParser.h"

using namespace gem;

bool
Insn::
set_format(const std::string& format_name, const format::FrmtList& formats)
{
    this->format_id = format_name;

    for (auto& frmt : formats)
    {
        if (format_name == frmt.get_name())
        {
            this->format = &frmt;
            return true;
        }
    }

    return false;
}

bool
Insn::
set_field(const std::string& field_name, const std::string& val_str)
{
    if (val_str.empty()) return false;

    int base{0};
    switch (val_str[0]) {
        case 'b': base = 2; break;
        case 'h': base = 16; break;
        case 'd': base = 10; break;
        case 'o': base = 8; break;
    }

    int64_t val = base?
        std::stoll(val_str.substr(1), nullptr, base):
        std::stoll(val_str,           nullptr, 2);

    //log(DBG) << "field:" << field_name << " value:" << val_str << "=" << val << "\n";
 
    return true;
}

void
Insns::
read_insn_file(const std::string& file_name)
{
    log(INFO) << "Reading instrucition file " << file_name << " ...\n";

    auto xml_text = File::read(file_name);

    xml::Parser parser;

    auto on_start = [&](
        xml::Parser::Path const& path,
        xml::string const& tag,
        xml::Parser::AttrList const& attrs
        )->void
    {
        if (path.empty()) return;

        auto owner = path.back();

        if (tag == "insn")
        {
            if (owner == "insns")
            {
                m_insns.emplace_back("mn?", "name?");
            }
            else
                throw std::runtime_error(std::string("'insn' does not belong ")+owner);
        }

    };

    auto on_end = [&](
        xml::Parser::Path const& path, xml::string const& tag,
        xml::string::size_type content_begin, xml::string::size_type content_size
        )->void
    {
        if (path.empty()) return;

        auto owner = path.back();

        if (tag == "mn") {
            auto mn = xml_text.substr(content_begin, content_size);
            if (owner == "insn") {
                m_insns.back().mn = mn;
            }
        } 
        else if (tag == "name") {
            auto name = xml_text.substr(content_begin, content_size);
            if (owner == "insn") {
                m_insns.back().name = name;
            }
        }
        else if (tag == "format") {
            auto format = xml_text.substr(content_begin, content_size);
            if (owner == "insn") {
                m_insns.back().set_format(format, m_formats.get_formats_list());
            }
        }
        else if (tag == "insn") {
            if (owner == "insns") {
                //TODO post-processing, finalize
            }
        }
        else if (tag == "decode") {}
        else
        {
            if (owner == "decode") {
                auto field_name = tag;
                auto val_str = xml_text.substr(content_begin, content_size);
                m_insns.back().set_field(field_name, val_str);
            }
            else
                throw std::runtime_error(std::string("tag not handled:")+tag);
        }
    };

    try {
        parser.parse(xml_text, on_start, on_end);
    }
    catch (xml::exception& e) {
        log(ERR) << "EXCEPTION:" << e.what() << "\n";
    }

}

void
Insns::
read_insn_dir(const std::string& dir_name)
{
    log(INFO) << "Reading directory with instrucition files " << dir_name << " ...\n";

    std::string filter = ".+insn\\.xml" ;

    try
    {
    gem::Dir::scan(
        dir_name,
        [&](const std::string& fn, const std::string& fpath)->void {
            Insns::read_insn_file(fpath);
        },
        filter
    );

    }
    catch (std::regex_error& e)
    {
        log(ERR) << "regex exception:" << e.what() << "\n";
    }
}

void
Insns::
output()
{
    for (auto& insn : m_insns)
    {
        output_insn(insn);
    }
}

void
Insns::
output_insn(const Insn& insn)
{
    std::string file_name(insn.mn + ".html");
    log(DBG) << "outputing " << file_name << " ...\n";

    std::ofstream f;
    f.open(file_name);

    f <<
R"HTML(
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html>
<head>
<title>)HTML" << insn.mn << R"HTML(</title>
<STYLE TYPE="text/css">
<!--
TD{font-family: monospace; font-size: 10pt; width: 2em}
TR{text-align: center;}
-->
</STYLE>
</head>

<body>
)HTML";

    f <<
R"HTML(
<h2>Mnemonic: )HTML" << insn.mn << R"HTML(<h2>
<h2>Name: )HTML" << insn.name << R"HTML(<h2>
<h2>Format: )HTML" << insn.format_id << R"HTML(<h2>
)HTML";

    f <<
R"HTML(
  <table>
  <tr style="background-color:#cccccc">
)HTML";

    for (int i = insn.format->get_size() - 1; i >= 0; --i)
    {
        f << "<td>" << i << "</td>";
    }

    f << "</tr><tr>";
    for (auto& field : insn.format->get_fields())
    {
        f << "<td colspan=" << field.get_size() <<
        " style=\"background-color:" << field.get_color() << "\">" <<
        field.get_name() << "</td>";
   }

    f <<
R"HTML(
  </tr>
)HTML";

    f <<
R"HTML(
</body>

</html>
)HTML";

}

