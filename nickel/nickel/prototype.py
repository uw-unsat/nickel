import z3
import libirpy.util as util
import libirpy.typedefs as td


def arg(name, type):
    return (name, type)


def i64(name):
    return arg(name, td.uint64_t)


class Prototype(object):
    def __init__(self, prototypes):
        self._prototypes = prototypes

    def keys(self):
        return self._prototypes.keys()

    def _mktype(self, name, type, kwargs={}):
        if callable(type):
            return type(name, **kwargs)
        else:
            if ' ' in name:
                res = util.FreshConsts(name, type)
            else:
                res = util.FreshConst(name, type)

        if kwargs.get('concat', False):
            return z3.Concat(*res[::-1])
        return res

    def __getattr__(self, name):
        def inner():
            out = []
            signature = self._prototypes[name]
            for i in signature:
                out.append(self._mktype(*i))
            return tuple(out)

        if name in self._prototypes:
            return inner
        else:
            raise AttributeError(name)
