#pragma once

#include <iostream>

namespace irpy {

class Emitter
{
  protected:
    std::ostream &stream_;

    int indent_level_;

  public:
    Emitter(std::ostream &stream) : stream_(stream), indent_level_(0)
    {
    }
    Emitter(const Emitter &) = delete;
    Emitter &operator=(const Emitter &) = delete;

    void line(const std::string &) const;
    void line(void) const;
};

} // namespace irpy
