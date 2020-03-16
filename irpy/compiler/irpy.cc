#include "PyLLVMEmitter.hh"
#include <ctime>

static bool verbose;

inline static constexpr double cycles_to_ms(std::clock_t t) {
    return t / static_cast<double>(CLOCKS_PER_SEC / 1000.0);
}

int main(int argc, char **argv)
{

    llvm::LLVMContext ctx;
    llvm::SMDiagnostic err;
    const std::string filename = (argc < 2) ? "-" : std::string{argv[1]};

    std::clock_t start = std::clock();

    auto module = llvm::parseIRFile(filename, err, ctx);
    if (!module) {
        err.print("irpy", llvm::errs());
        return 3;
    }

    std::clock_t parsedone = std::clock();
    if (verbose)
        std::cerr << "Parsing took " << cycles_to_ms(parsedone - start) << " ms." << std::endl;

    irpy::PyLLVMEmitter emitter{std::cout, module.get()};

    emitter.emitWarning(filename);
    emitter.emitModule();

    std::clock_t emitdone = std::clock();
    if (verbose)
        std::cerr << "Emitting took " << cycles_to_ms(emitdone - parsedone) << " ms." << std::endl;

    return 0;
}
