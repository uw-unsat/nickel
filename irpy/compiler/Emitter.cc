#include "Emitter.hh"

#include <sstream>

namespace irpy {

void Emitter::line(const std::string &ref) const
{
    for (auto i = 0; i < indent_level_; ++i)
        stream_ << "  ";
    stream_ << ref << std::endl;
}

void Emitter::line(void) const
{
    stream_ << std::endl;
}

} // namespace irpy
