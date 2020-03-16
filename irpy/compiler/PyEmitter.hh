#pragma once

#include "Emitter.hh"

#include <tuple>
#include <iostream>
#include <vector>
#include <set>
#include <string>
#include <functional>

namespace irpy {

class PyEmitter : public Emitter
{

  public:
    PyEmitter(std::ostream &stream) : Emitter(stream)
    {
    }

    void genBlock(const std::string &blk, const std::function<void()> &body);

    void genDef(const std::string &name, const std::vector<std::string> &args,
                const std::function<void()> &func);

    void genException(const std::string &message) const;

    void emitWarning(const std::string &filename) const;

};

} // namespace irpy
