#ifndef translator_HEADER
#define translator_HEADER

class Translator {
    public :
        virtual ~Translator () {}
        virtual Instruction * translate (const uint8_t * data, size_t size) = 0;
};

#endif