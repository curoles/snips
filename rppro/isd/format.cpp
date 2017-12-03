/**@file
 * @brief     Instruction Format
 * @author    2013 Igor Lesik
 * @copyright 2013 Igor Lesik
 *
 */
#include "format.h"

#include <iostream>
//#include <algorithm>

#include "cgem/File.h"
#include "cgem/XMLParser.h"

using namespace gem;


void
format::Formats::
read_post_processing()
{
    for (auto& format : m_formats)
    {
        format.size = 0;

        for (auto& field : format.fields)
        {
            if (field.begin > field.end) throw std::runtime_error("field.begin > end");

            field.size = field.end - field.begin + 1;
            format.size += field.size;
        }

        //std::sort(format.fields.begin(), format.fields.end(), Field::less);
        format.fields.sort(Field::greater);
    }

}

void
format::Formats::
read(const char* file_name)
{
    log << "reading " << file_name << " ...\n";

    auto xml_text = File::read(file_name);

    xml::Parser parser;

    auto on_start = [&](
        xml::Parser::Path const& path, xml::string const& tag, xml::Parser::AttrList const& attrs
        )->void
    {
        if (path.empty()) return;

        auto owner = path.back();

        if (tag == "format")
        {
            if (owner == "formats")
            {
                m_formats.push_back(Format());
            }
            else if (owner == "group")
            {
                m_formats.push_back(Format());

                //m_groups.back().push_back(Format());
            }
            else
                throw std::runtime_error(std::string("'format' does not belong ")+owner);
        }
        else if (tag == "f")
        {
            if (owner == "format")
            {
                m_formats.back().fields.push_back(Field());
            }
            else if (owner == "group")
            {
                m_groups.back().fields.push_back(Field());
            }
            else if (owner == "def")
            {
                m_defs.back().fields.push_back(Field());
            }
            else
                throw std::runtime_error(std::string("'field' does not belong ")+owner);
        }
        if (tag == "group")
        {
            if (owner == "formats")
            {
                m_groups.push_back(Group());
            }
            else
                throw std::runtime_error(std::string("'group' does not belong ")+owner);
        }
        if (tag == "def")
        {
            if (owner == "formats")
            {
                m_defs.push_back(Format());
            }
            else
                throw std::runtime_error(std::string("'def' does not belong ")+owner);
        }

    };

    auto on_end = [&](
        xml::Parser::Path const& path, xml::string const& tag,
        xml::string::size_type content_begin, xml::string::size_type content_size
        )->void
    {
        if (path.empty()) return;

        auto owner = path.back();

        if (tag == "name") {
            auto name = xml_text.substr(content_begin, content_size);
            if (owner == "f") {
                auto fld_owner = *(++path.rbegin());
                if (fld_owner == "format") m_formats.back().fields.back().name = name;
                else if (fld_owner == "def") m_defs.back().fields.back().name = name;
                else if (fld_owner == "group") m_groups.back().fields.back().name = name;
            }
            else if (owner == "format") { m_formats.back().name = name; }
            else if (owner == "def") { m_defs.back().name = name; }
            else if (owner == "group") { m_groups.back().name = name; }
            else if (owner == "formats") { m_name = name; }
        } 
        else if (tag == "begin" or tag == "end") {
            auto pos_str = xml_text.substr(content_begin, content_size);
            std::size_t pos = strtoull(pos_str.c_str(), nullptr, 0);
            if (owner == "f") {
                auto fld_owner = *(++path.rbegin());
                Field* field = nullptr;
                if (fld_owner == "format") field = &m_formats.back().fields.back();
                else if (fld_owner == "def") field = &m_defs.back().fields.back();
                else if (fld_owner == "group") field = &m_groups.back().fields.back();

                if (tag == "begin") field->begin = pos; else field->end = pos;
            }
        } 
        else if (tag == "color") {
            auto color = xml_text.substr(content_begin, content_size);
            if (owner == "f") {
                auto fld_owner = *(++path.rbegin());
                Field* field = nullptr;
                if (fld_owner == "format") field = &m_formats.back().fields.back();
                else if (fld_owner == "def") field = &m_defs.back().fields.back();
                else if (fld_owner == "group") field = &m_groups.back().fields.back();

                field->color = color;
            }
        } 
        else if (tag == "val") {
            auto val_str = xml_text.substr(content_begin, content_size);
            if (owner == "f") {
                auto fld_owner = *(++path.rbegin());
                Field* field = nullptr;
                if (fld_owner == "format") field = &m_formats.back().fields.back();
                else if (fld_owner == "def") field = &m_defs.back().fields.back();
                else if (fld_owner == "group") field = &m_groups.back().fields.back();

                field->val_str = val_str;
            }
        } 
        else if (tag == "is") {
            auto definition = xml_text.substr(content_begin, content_size);
            if (owner == "f") {
                auto fld_owner = *(++path.rbegin());
                Field* field = nullptr;
                if (fld_owner == "format") field = &m_formats.back().fields.back();
                else if (fld_owner == "def") field = &m_defs.back().fields.back();
                else if (fld_owner == "group") field = &m_groups.back().fields.back();

                field->definition = definition;
            }
        }
        else if (tag == "format") {
            if (owner == "group") {
                Group& group = m_groups.back();
                for (auto& field : group.fields) {
                    m_formats.back().fields.push_back(field);
                }
            }
        } 

    };

    try {
        parser.parse(xml_text, on_start, on_end);
    }
    catch (xml::exception& e) {
        std::cout << "EXCEPTION:" << e.what() << "\n";
    }

    read_post_processing();
}

void
format::Formats::
output(const char* file_name)
{
    gem::File f;
    if (not f.open(file_name, "w"))
    {
        log << "could not open " << file_name << "\n";
        return;
    }

    log << "creating " << file_name << " ...\n";

fprintf(f, R"HTML(
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html>
<head>
<title>Formats</title>
<STYLE TYPE="text/css">
<!--
TD{font-family: monospace; font-size: 10pt; width: 2em}
TR{text-align: center;}
--->
</STYLE>
</head>

<body>
  <h1>%s Instruction Formats</h1>
)HTML", m_name.c_str());

for (auto format : m_formats)
{
fprintf(f, R"HTML(
  <h2>Format %s</h2>
)HTML", format.name.c_str());


fprintf(f, R"HTML(
  <table>
  <tr style="background-color:#cccccc">
)HTML");
    for (int i = format.get_size() - 1; i >= 0; --i)
    {
fprintf(f, R"HTML(<td>%u</td>)HTML", i);
    }

fprintf(f, R"HTML(
  </tr>
  <tr>
)HTML");

  for (auto& field : format.fields)
  {
fprintf(f, R"HTML(
    <td colspan="%lu" style="background-color:%s">%s</td>
)HTML", field.size, field.color.c_str(), field.name.c_str());
  }

fprintf(f, R"HTML(
  </tr>
  <tr style="background-color:#cccccc">
)HTML");

  for (auto& field : format.fields)
  {
      std::string comment;
      if (field.has_val()) { comment = field.val_str; }
      else if (field.has_definition()) { comment = field.definition; }
fprintf(f, R"HTML(
    <td colspan="%lu" style="background-color:%s">%s</td>
)HTML", field.size, field.color.c_str(), comment.c_str());
  }

fprintf(f, R"HTML(
  </tr>
  </table>
)HTML");

}

fprintf(f, R"HTML(
</body>

</html>
)HTML");

}

