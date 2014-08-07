#ifndef machine_HEADER
#define machine_HEADER

#include <string>
#include <inttypes.h>

class Register {
    private :
        std::string name;
        uint64_t value;
    public :
        Register (std::string name) name (name) {}

        void     s_value (uint64_t value) { this->value = value; }
        uint64_t g_value ()               { return value; }
};

class Machine {
    private :
        Translator translator;
        std::map <std::string, Register> registers;
        std::map <uint64_t, uint8_t>     memory;
        std::string ip_name

    public :
        Machine (Translator & translator,
                 std::string  ip_name)
            : Translator (translator),
              ip_name (ip_name) {}

        void     s_memory   (uint64_t address, const uint8_t * data, size_t size);
        uint8_t  g_memory   (uint64_t address);
        void     s_register (std::string name, uint64_t value);
        uint64_t g_register (std::string name);

        void concrete_step ();
};

#endif