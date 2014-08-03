#include "x86queso.h"

#include "generic_instructions.h"

#include <iostream>
#include <stdexcept>
#include <sstream>
#include <cstdio>

Instruction * QuesoX86 :: translate (const uint8_t * data, size_t size, uint64_t address) {
    if (ix86 != NULL)
        delete ix86;
    this->address = address;

    ud_init(&ud_obj);
    ud_set_mode(&ud_obj, 32);
    ud_set_syntax(&ud_obj, UD_SYN_INTEL);

    ud_set_input_buffer(&ud_obj, (unsigned char *) data, size);

    if (ud_disassemble(&ud_obj) == 0)
        return NULL;

    ix86 = new InstructionX86(ud_insn_asm(&ud_obj));

    switch (ud_obj.mnemonic) {
    case UD_Iadd : add(); break;
    case UD_Iand : And(); break;
    default :
        break;
    }

    return ix86;
}


Variable fullReg (unsigned int reg) {
    switch (reg) {
    case UD_R_AL :
    case UD_R_AH :
    case UD_R_AX :
    case UD_R_EAX :
        return Variable(32, "eax");
    case UD_R_BL :
    case UD_R_BH :
    case UD_R_BX :
    case UD_R_EBX :
        return Variable(32, "ebx");
    case UD_R_CL :
    case UD_R_CH :
    case UD_R_CX :
    case UD_R_ECX :
        return Variable(32, "ecx");
    case UD_R_DL :
    case UD_R_DH :
    case UD_R_DX :
    case UD_R_EDX :
        return Variable(32, "edx");
    case UD_R_ESP :
        return Variable(32, "esp");
    case UD_R_EBP :
        return Variable(32, "ebp");
    }
    throw std::runtime_error("invalid register " + reg);
}


Variable QuesoX86 :: getRegister (unsigned int reg) {
    switch (reg) {
    case UD_R_AH :
    case UD_R_BH :
    case UD_R_CH :
    case UD_R_DH : {
        Variable rh = 
            (reg == UD_R_AH ? Variable(8, "ah") :
             (reg == UD_R_BH ? Variable(8, "bh") :
              (reg == UD_R_CH ? Variable(8, "ch") :
               (reg == UD_R_DH ? Variable(8, "dh") :
                Variable(0, "error")))));
        Constant eight = Constant(32, 8);
        Variable fullreg = fullReg(reg);
        Variable tmp = Variable(32, "tmpGetRegister");
        ix86->pdi(new InstructionShr(tmp, fullreg, eight));
        ix86->pdi(new InstructionAssign(rh, tmp));
        return rh;
    }
    case UD_R_AL :
    case UD_R_BL :
    case UD_R_CL :
    case UD_R_DL : {
        Variable rl = 
            (reg == UD_R_AL ? Variable(8, "al") :
             (reg == UD_R_BL ? Variable(8, "bl") :
              (reg == UD_R_CL ? Variable(8, "cl") :
               (reg == UD_R_DL ? Variable(8, "dl") :
                Variable(0, "error")))));
        ix86->pdi(new InstructionAssign(rl, fullReg(reg)));
        return rl;
    }
    case UD_R_AX :
    case UD_R_BX :
    case UD_R_CX :
    case UD_R_DX : {
        Variable rx = 
            (reg == UD_R_AX ? Variable(16, "ax") :
             (reg == UD_R_BX ? Variable(16, "bx") :
              (reg == UD_R_CX ? Variable(16, "cx") :
               (reg == UD_R_DX ? Variable(16, "dx") :
                Variable(0, "error")))));
        ix86->pdi(new InstructionAssign(rx, fullReg(reg)));
        return rx;
    }
    case UD_R_EAX :
    case UD_R_EBX :
    case UD_R_ECX :
    case UD_R_EDX :
    case UD_R_ESP :
    case UD_R_EBP :
        return fullReg(reg);
    }
    throw std::runtime_error("unknown register");
}


Constant QuesoX86 :: operand_lval (unsigned int bits, ud_operand operand) {
    switch (bits) {
    case 8  : return Constant(8, operand.lval.ubyte);
    case 16 : return Constant(16, operand.lval.uword);
    case 32 : return Constant(32, operand.lval.udword);
    default :
        throw std::runtime_error("invalid operand_lval offset");
    }
    return Constant(0, 0);
}


Operand * QuesoX86 :: sib (ud_operand operand) {
    Variable base(0, "");
    Variable index(0, "");
    Constant scale(0, 0);
    Constant displ(0, 0);

    if (operand.base)
        base = getRegister(operand.base);
    if (operand.index)
        index = getRegister(operand.index);
    if (operand.scale)
        scale = Constant(index.g_bits(), operand.scale);
    if (operand.offset)
        displ = operand_lval(operand.offset, operand);

    Variable index_scale = index;
    if (operand.index && operand.scale) {
        index_scale = Variable(index_scale.g_bits(), "index_scale");
        ix86->pdi(new InstructionMul(index_scale, index, scale));
    }

    if (operand.base) {
        if (operand.offset) {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, base, index_scale));
                ix86->pdi(new InstructionAdd(sib, sib, displ));
                return sib.copy();
            }
            // (operand.base) (operand.offset) (! operand.index)
            else {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, base, displ));
                return sib.copy();
            }
        }
        else {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, base, index_scale));
                return sib.copy();
            }
            else
                return base.copy();
        }
    }
    else {
        if (operand.offset) {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, index_scale, displ));
                return sib.copy();
            }
            // (! operand.base) (operand.offset) (! operand.index)
            else
                return displ.copy();
        }
        else
            return index_scale.copy();
    }
}


Operand * QuesoX86 :: operandGet (unsigned int place) {
    struct ud_operand operand = ud_obj.operand[place];

    if (operand.type == UD_OP_REG)
        return getRegister(operand.base).copy();
    else if (operand.type == UD_OP_MEM) {
        Operand * address = sib(operand);
        Variable loaded(operand.size, "loaded");
        Array memory(8, "memory", 32);
        switch (operand.size) {
        case 8  : ix86->pdi(new InstructionLoad(&loaded, &memory, address)); break;
        case 16 : ix86->pdi(new InstructionLoadLE16(&loaded, &memory, address)); break;
        case 32 : ix86->pdi(new InstructionLoadLE32(&loaded, &memory, address)); break;
        default : throw std::runtime_error("UD_OP_MEM with invalid operand size");
        }
        delete address;
        return loaded.copy();
    }
    else if (    (operand.type == UD_OP_CONST)
              || (operand.type == UD_OP_JIMM)
              || (operand.type == UD_OP_IMM))
        return operand_lval(operand.size, operand).copy();

    throw std::runtime_error("invalid operand type ");
}


void QuesoX86 :: operandSet (unsigned int place, Operand * value) {
    struct ud_operand operand = ud_obj.operand[place];

    if (operand.type == UD_OP_REG) {
        switch (operand.base) {
        case UD_R_AH :
        case UD_R_BH :
        case UD_R_CH :
        case UD_R_DH :
            throw std::runtime_error("setting ah/bh/cd/dh unsupported");
            return;
        default :
            break;
        }
        Variable fullreg = fullReg(operand.base);
        ix86->pdi(new InstructionAssign(&fullreg, value));
        return;
    }
    else if (operand.type == UD_OP_MEM) {
        Operand * address = sib(operand);
        Array memory(8, "memory", 32);
        switch (operand.size) {
        case 8  : ix86->pdi(new InstructionStore(&memory, address, value)); break;
        case 16 : ix86->pdi(new InstructionStoreLE16(&memory, address, value)); break;
        case 32 : ix86->pdi(new InstructionStoreLE32(&memory, address, value)); break;
        default : throw std::runtime_error("operandSet invalid operand size");
        }
        delete address;
    }
}


bool QuesoX86 :: cmovcc (const Operand * condition) {
    Variable * dst = dynamic_cast<Variable *> (operandGet(0));
    Operand * src = operandGet(1);

    ix86->pdi(new InstructionIte(dst, condition, src, dst));

    delete dst;
    delete src;

    return true;
}

    
bool QuesoX86 :: add () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp = Variable(lhs->g_bits(), "tmp");
    Constant zero = Constant(lhs->g_bits(), 0);
    Variable OF = Variable(1, "OF");
    Variable SF = Variable(1, "SF");
    Variable CF = Variable(1, "CF");
    Variable ZF = Variable(1, "ZF");

    ix86->pdi(new InstructionAdd(&tmp, lhs, rhs));
    ix86->pdi(new InstructionCmpLtu(&CF, &tmp, lhs));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));

    Variable SFxorOF = Variable(1, "SFxorOF");
    ix86->pdi(new InstructionCmpLts(&SFxorOF, lhs, rhs));
    ix86->pdi(new InstructionXor(&OF, &SFxorOF, &SF));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


    
bool QuesoX86 :: And () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp = Variable(lhs->g_bits(), "tmp");

    Constant zero1 = Constant(1, 0);
    Constant zeroBits = Constant(lhs->g_bits(), 0);
    Variable OF = Variable(1, "OF");
    Variable SF = Variable(1, "SF");
    Variable CF = Variable(1, "CF");
    Variable ZF = Variable(1, "ZF");

    // 8-bit immediates are always sign-extended
    if ((ud_obj.operand[1].type == UD_OP_IMM) && (rhs->g_bits() == 8)) {
        Operand * rhs_old = rhs;
        Variable * rhs = new Variable(lhs->g_bits(), "tmpRhs");
        ix86->pdi(new InstructionSignExtend(rhs, rhs_old));
        delete rhs_old;
    }

    ix86->pdi(new InstructionAnd(&tmp, lhs, rhs));

    ix86->pdi(new InstructionAssign(OF, zero1));
    ix86->pdi(new InstructionAssign(CF, zero1));
    ix86->pdi(new InstructionCmpEq(ZF, tmp, zeroBits));
    ix86->pdi(new InstructionCmpLts(SF, tmp, zeroBits));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: cmova () {
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Variable CF(1, "CF");
    Variable notCF(1, "notCF");
    Variable notCFandnotZF(1, "notCFandnotZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(notZF, ZF, one));
    ix86->pdi(new InstructionXor(notCF, CF, one));
    ix86->pdi(new InstructionAnd(notCFandnotZF, notZF, notCF));

    return cmovcc(notCFandnotZF);
}


bool QuesoX86 :: cmovb () {
    return cmovcc(Variable(1, "CF"));
}


bool QuesoX86 :: cmovbe () {
    Variable ZF(1, "ZF");
    Variable CF(1, "CF");
    Variable CForZF(1, "CForZF");

    ix86->pdi(new InstructionOr(CForZF, CF, ZF));

    return cmovcc(CForZF);
}


bool QuesoX86 :: cmovnz () {
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(notZF, ZF, one));

    return cmovcc(notZF);
}


bool QuesoX86 :: cmovs () {
    return cmovcc(Variable(1, "SF"));
}


bool QuesoX86 :: cmovz () {
    return cmovcc(Variable(1, "ZF"));
}


bool QuesoX86 :: cmp () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);

    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFxorOF(1, "SFxorOF");
    Variable tmp(lhs->g_bits(), "tmp");
    Constant zero(lhs->g_bits(), 0);

    Variable sext(lhs->g_bits(), "sext");
    ix86->pdi(new InstructionSignExtend(&sext, rhs));

    ix86->pdi(new InstructionCmpLtu(&CF,          lhs, &sext));
    ix86->pdi(new InstructionCmpLts(&SFxorOF,     lhs, &sext));
    ix86->pdi(new InstructionCmpEq (&ZF,          lhs, &sext));
    ix86->pdi(new InstructionSub   (&tmp,         lhs, &sext));
    ix86->pdi(new InstructionCmpLts(&SF,          &tmp, &zero));
    ix86->pdi(new InstructionXor   (&OF,          &SFxorOF, &SF));

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: cwde () {
    Variable ax = getRegister(UD_R_AX);
    Variable eax = getRegister(UD_R_EAX);

    ix86->pdi(new InstructionSignExtend(eax, ax));

    return true;
}