/**@file
 * @brief     Instruction Format
 * @author    2013 Igor Lesik
 * @copyright 2013 Igor Lesik
 *
 */
#pragma once

#include <string>
#include <list>

#include "logging.h"

namespace format {

class Field
{
private:
    std::string name;
    std::string color;
    std::size_t begin, end, size;

    std::string val_str;
    uint32_t val;

    std::string definition;

public:
    Field(const std::string& name="", const std::string& color="red",
          std::size_t begin=0, std::size_t end=0):
        name(name), color(color), begin(begin), end(end)
    {
        size = end - begin;
    }

    static
    struct OpLess{ bool operator()(const Field& a, const Field& b) {
        return a.begin < b.begin;
    }} less;

    static
    struct OpMore{ bool operator()(const Field& a, const Field& b) {
        return a.begin > b.begin;
    }} greater;

    bool has_val() const { return !val_str.empty(); }
    bool has_definition() const { return !definition.empty(); }

    const std::string& get_name() const { return name; }
    const std::string& get_color() const { return color; }
    const std::size_t get_size() const { return size; }

    friend class Formats;
};

class Format
{
public:
    typedef std::list<Field> Fields;

private:
    Fields      fields;
    std::string name;
    std::size_t size;

public:
    std::size_t get_size() const { return size; }

    const std::string& get_name() const { return name; }

    const Fields& get_fields() const { return fields; }

    friend class Formats;
};

class Group
{
public:
    typedef std::list<Field>  Fields;

private:
    Fields    fields;

    std::string name;

    friend class Formats;
};

typedef std::list<Format> FrmtList;

class Formats
{
public:
    typedef std::list<Group>  GroupList;

private:
    FrmtList  m_formats;
    FrmtList  m_defs;
    GroupList m_groups;

    std::string m_name;

    Log& log;

public:
    Formats():log(get_logger()){}

    const FrmtList& get_formats_list() const {return m_formats;}

public:
    void read(const char* file_name);
    void read_post_processing();
    void output(const char* file_name);
};

} // end namespace format

