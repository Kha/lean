/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "util/priority_queue.h"

#ifndef LEAN_DEFAULT_PRIORITY
#define LEAN_DEFAULT_PRIORITY 1000u
#endif

namespace lean {

struct attr_data {
    virtual unsigned hash() const {
        return 0;
    }
};

typedef std::shared_ptr<attr_data> attr_data_ptr;
struct attr_config;

class attribute {
    friend struct attr_config;
private:
    std::string m_id;
    std::string m_descr;
    std::string m_token;
protected:
    environment set_core(environment const &, io_state const &, name const &, attr_data_ptr, bool) const;
    virtual void write_entry(serializer &, attr_data const &) const = 0;
    virtual std::unique_ptr<attr_data> read_entry(deserializer &) const = 0;
public:
    attribute(char const * id, char const * descr) : m_id(id), m_descr(descr), m_token(std::string("[") + id) {}
    std::string const & get_name() const { return m_id; }
    std::string const & get_token() const { return m_token; }
};

typedef std::shared_ptr<attribute const> attribute_ptr;

/** \brief An attribute without associated data or priority declaration */
class basic_attribute : public attribute {
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual std::unique_ptr<attr_data> read_entry(deserializer &) const override final { return {}; }
public:
    basic_attribute(char const * id, char const * descr) : attribute(id, descr) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, bool persistent) const {
        return set_core(env, ios, n, attr_data_ptr(new attr_data), persistent);
    }
};

// TODO(sullrich): Let the attribute handle priority parsing itself by introducing a custom
// syntax (something like [attr:prio]?)
class prio_attribute : public attribute {
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual std::unique_ptr<attr_data> read_entry(deserializer &) const override final { return {}; }
public:
    prio_attribute(char const * id, char const * descr) : attribute(id, descr) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, unsigned prio,
                            bool persistent) const;
};

template<typename Data>
class typed_attribute : public attribute {
protected:
    virtual void write_entry(serializer & s, attr_data const & data) const final override {
        lean_assert(dynamic_cast<Data const *>(&data));
        write_entry_typed(s, static_cast<Data const &>(data));
    }
    virtual std::unique_ptr<attr_data> read_entry(deserializer & d) const final override {
        return std::unique_ptr<attr_data>(new Data(read_entry_typed(d)));
    }

    virtual void write_entry_typed(serializer & s, Data const & data) const = 0;
    virtual Data read_entry_typed(deserializer & d) const = 0;
public:
    typed_attribute(char const * id, char const * descr) : attribute(id, descr) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, Data data, bool persistent) const {
        return set_core(env, ios, n, std::unique_ptr<attr_data>(new Data(data)), persistent);
    }
};

struct unsigned_params_attribute_data : public attr_data {
    list<unsigned> m_params;
    unsigned_params_attribute_data(list<unsigned> const & params) : m_params(params) {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (unsigned i : m_params)
            h = ::lean::hash(h, i);
        return h;
    }
};

class unsigned_params_attribute : public typed_attribute<unsigned_params_attribute_data> {
    typedef unsigned_params_attribute_data data;

    virtual void write_entry_typed(serializer & s, data const & data) const override {
        write_list(s, data.m_params);
    }
    virtual data read_entry_typed(deserializer & d) const override {
        return { read_list<unsigned>(d) };
    }
public:
    unsigned_params_attribute(char const * id, char const * descr) : typed_attribute(id, descr) {}
};

void register_attribute(attribute_ptr);

template<typename Attribute>
void register_attribute(Attribute attr) {
    register_attribute(attribute_ptr(new Attribute(attr)));
}

typedef std::function<environment(environment const &, io_state const &, name const &,
                                  bool)> set_no_params_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  unsigned, bool)> set_prio_attribute_proc;

// legacy/convenience(?) register functions
void register_no_params_attribute(char const * attr, char const * descr, set_no_params_attribute_proc const & on_set);
void register_no_params_attribute(char const * attr, char const * descr);
void register_prio_attribute(char const * attr, char const * descr, set_prio_attribute_proc const & on_set);
void register_prio_attribute(char const * attr, char const * descr);
void register_unsigned_params_attribute(char const *attr, char const *descr);

void register_incompatible(char const * attr1, char const * attr2);

// TODO(sullrich): all of these should become members of/return attribute or a subclass
bool is_attribute(std::string const & attr);
void get_attributes(buffer<char const *> &);
void get_attribute_tokens(buffer<char const *> &);
char const * get_attribute_from_token(char const * attr_token);
char const * get_attribute_token(char const * attr);

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, unsigned prio, list<unsigned> const & params, bool persistent);
environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, bool persistent);

bool has_attribute(environment const & env, char const * attr, name const & d);
void get_attribute_instances(environment const & env, name const & attr, buffer<name> &);
priority_queue<name, name_quick_cmp> get_attribute_instances_by_prio(environment const & env, name const & attr);

unsigned get_attribute_prio(environment const & env, std::string const & attr, name const & d);
list<unsigned> get_attribute_params(environment const & env, std::string const & attr, name const & d);

bool are_incompatible(char const * attr1, char const * attr2);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
