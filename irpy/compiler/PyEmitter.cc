#include "PyEmitter.hh"

#include <sstream>

namespace irpy {

void PyEmitter::genBlock(const std::string &blk, const std::function<void()> &body)
{
    this->line(blk + ":");
    ++indent_level_;
    body();
    --indent_level_;
}

void PyEmitter::genDef(const std::string &name, const std::vector<std::string> &args,
                       const std::function<void()> &func)
{
    std::ostringstream def;
    def << "def " << name << "(";
    for (auto &a : args)
        def << a << ",";
    def << ")";
    this->genBlock(def.str(), func);
    this->line();
}

void PyEmitter::emitWarning(const std::string &filename) const
{
    this->line("#");
    this->line("# WARNING: This file has been automatically generated from " + filename);
    this->line("#");
    this->line();
}

void PyEmitter::genException(const std::string &message) const
{
    this->line("raise Exception('" + message + ")");
    this->line();
}

} // namespace irpy
