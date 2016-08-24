/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/abstract_parser.h"
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
    virtual void parse(abstract_parser &) {}
    virtual void print(std::ostream &) {}
    virtual ~attr_data() {}
};

typedef std::shared_ptr<attr_data> attr_data_ptr;
struct attr_config;

typedef std::function<environment(environment const &, io_state const &, name const &, unsigned, bool)> after_set_proc;
typedef std::function<void(environment const &, name const &, bool)> after_set_check_proc;
typedef std::function<environment(environment const &, name const &, bool)> before_unset_proc;

class attribute {
    friend struct attr_config;
    friend class  decl_attributes;
private:
    name              m_id;
    std::string       m_descr;
    after_set_proc    m_after_set;
    before_unset_proc m_before_unset;
protected:
    environment set_core(environment const &, io_state const &, name const &, unsigned, attr_data_ptr, bool) const;

    virtual environment set_untyped(environment const &, io_state const &, name const &, unsigned, attr_data_ptr, bool) const = 0;
    virtual void write_entry(serializer &, attr_data const &) const = 0;
    virtual attr_data_ptr read_entry(deserializer &) const = 0;
public:
    attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            m_id(id), m_descr(descr), m_after_set(after_set), m_before_unset(before_unset) {}
    virtual ~attribute() {}

    name const & get_name() const { return m_id; }
    std::string const & get_description() const { return m_descr; }

    virtual attr_data_ptr get_untyped(environment const &, name const &) const;
    bool is_instance(environment const & env, name const &n ) const {
        return static_cast<bool>(get_untyped(env, n));
    }
    unsigned get_prio(environment const &, name const &) const;
    virtual void get_instances(environment const &, buffer<name> &) const;
    priority_queue<name, name_quick_cmp> get_instances_by_prio(environment const &) const;
    virtual attr_data_ptr parse_data(abstract_parser &) const;

    virtual environment unset(environment env, io_state const & ios, name const & n, bool persistent) const;
    virtual unsigned get_fingerprint(environment const & env) const;
};

typedef std::shared_ptr<attribute const> attribute_ptr;

/** \brief An attribute without associated data */
class basic_attribute : public attribute {
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual attr_data_ptr read_entry(deserializer &) const override final { return attr_data_ptr(new attr_data); }
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, unsigned prio, attr_data_ptr,
                                    bool persistent) const override final {
        return set(env, ios, n, prio, persistent);
    }
public:
    basic_attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            attribute(id, descr, after_set, before_unset) {}

    static basic_attribute with_check(name const & id, char const * descr, after_set_check_proc after_set) {
        return basic_attribute(
                id, descr,
                [=](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                    after_set(env, n, persistent);
                    return env;
                },
                [](environment const & env, name const &, bool) {
                    return env;
                });
    }

    virtual environment set(environment const & env, io_state const & ios, name const & n, unsigned prio, bool persistent) const {
        return set_core(env, ios, n, prio, attr_data_ptr(new attr_data), persistent);
    }
};

template<typename Data>
class typed_attribute : public attribute {
protected:
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, unsigned prio,
                                    attr_data_ptr data, bool persistent) const final override {
        lean_assert(dynamic_cast<Data const *>(&*data));
        return set(env, ios, n, prio, static_cast<Data const &>(*data), persistent);
    }

    virtual void write_entry(serializer & s, attr_data const & data) const final override {
        lean_assert(dynamic_cast<Data const *>(&data));
        static_cast<Data const &>(data).write(s);
    }
    virtual attr_data_ptr read_entry(deserializer & d) const final override {
        auto data = new Data;
        data->read(d);
        return attr_data_ptr(data);
    }
public:
    typed_attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            attribute(id, descr, after_set, before_unset) {}

    virtual attr_data_ptr parse_data(abstract_parser & p) const final override {
        auto data = new Data;
        data->parse(p);
        return attr_data_ptr(data);
    }

    virtual environment set(environment const & env, io_state const & ios, name const & n, unsigned prio,
                            Data const & data, bool persistent) const {
        return set_core(env, ios, n, prio, std::unique_ptr<attr_data>(new Data(data)), persistent);
    }
    std::shared_ptr<Data> get(environment const & env, name const & n) const {
        auto data = get_untyped(env, n);
        if (!data)
            return {};
        lean_assert(std::dynamic_pointer_cast<Data>(data));
        return std::static_pointer_cast<Data>(data);
    }
};

struct indices_attribute_data : public attr_data {
    list<unsigned> m_idxs;
    indices_attribute_data(list<unsigned> const & idxs) : m_idxs(idxs) {}
    indices_attribute_data() : indices_attribute_data(list<unsigned>()) {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (unsigned i : m_idxs)
            h = ::lean::hash(h, i);
        return h;
    }
    void write(serializer & s) const {
        write_list(s, m_idxs);
    }
    void read(deserializer & d) {
        m_idxs = read_list<unsigned>(d);
    }
    void parse(abstract_parser & p) override;
    virtual void print(std::ostream & out) override {
        for (auto p : m_idxs) {
            out << " " << p + 1;
        }
    }
};

template class typed_attribute<indices_attribute_data>;
/** \brief Attribute that represents a list of indices. input and output are 1-indexed for convenience. */
typedef typed_attribute<indices_attribute_data> indices_attribute;

class user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env);
    virtual void write_entry(serializer &, attr_data const &) {}
    virtual attr_data_ptr read_entry(deserializer &) {
        return attr_data_ptr(new attr_data);
    }
};

/** \brief Register the user_attribute handlers, if included in the compilation */
void set_user_attribute_ext(std::unique_ptr<user_attribute_ext>);

void register_system_attribute(attribute_ptr);
template<typename Attribute>
void register_system_attribute(Attribute attr) {
    register_system_attribute(attribute_ptr(new Attribute(attr)));
}
void register_incompatible(char const * attr1, char const * attr2);

bool is_attribute(environment const & env, name const & attr);
attribute const & get_attribute(environment const & env, name const & attr);
attribute const & get_system_attribute(name const & attr);
void get_attributes(environment const & env, buffer<attribute const *> &);

bool has_attribute(environment const & env, name const & attr, name const & d);

bool are_incompatible(attribute const & attr1, attribute const & attr2);

unsigned get_attribute_fingerprint(environment const & env, name const & attr);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
