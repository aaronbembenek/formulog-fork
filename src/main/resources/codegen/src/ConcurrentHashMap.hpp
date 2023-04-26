//
// Created by Aaron Bembenek on 4/25/23.
//

#pragma once

#include <libcuckoo/cuckoohash_map.hh>
#include <oneapi/tbb/concurrent_unordered_map.h>

namespace flg {

template<typename Key, typename Value, typename Hash, typename Equals>
class LibcuckooWrapper {
public:
    struct iterator {
        iterator(): opt({}) {}
        iterator(const Key &key, const Value &value) : opt({key, value}) {}

        friend bool operator==(const iterator &i1, const iterator &i2) {
            return i1.opt.has_value() == i2.opt.has_value();
        }

        friend bool operator!=(const iterator &i1, const iterator &i2) {
            return i1.opt.has_value() != i2.opt.has_value();
        }

        std::pair<Key, Value> *operator->() {
            return &opt.value();
        }

    private:
        std::optional<std::pair<Key, Value>> opt;
    };

    iterator find(const Key &key) {
        Value val;
        if (inner.find(key, val)) {
            return iterator(key, val);
        }
        return end();
    }

    template<typename K, typename... Args>
    std::pair<iterator, bool> emplace(K &&key, Args &&... args) {
        if (inner.insert(key, args...)) {
            return {iterator(key, Value{args...}), true};
        }
        return {find(key), false};
    }

    iterator end() {
        return iterator();
    }

private:
    libcuckoo::cuckoohash_map<Key, Value, Hash, Equals> inner;
};

/*
template<typename Key, typename Value, typename Hash = std::hash<Key>, typename Equals = std::equal_to<Key>>
using ConcurrentHashMap = tbb::concurrent_unordered_map<Key, Value, Hash, Equals>;
*/

template<typename Key, typename Value, typename Hash = std::hash<Key>, typename Equals = std::equal_to<Key>>
using ConcurrentHashMap = LibcuckooWrapper<Key, Value, Hash, Equals>;

}