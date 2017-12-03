/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_IR_H_INCLUDED
#define COH_IR_H_INCLUDED

#include "String.h"
#include "List.h"

typedef struct IrClassMemberVar
{
    String name;
    String type;
} IrClassMemberVar;

static inline void IrClassMemberVar_create(
    IrClassMemberVar* self,
    const char* name,
    const char* type
)
{
    String_create(&self->name, 0, name);
    String_create(&self->type, 0, type);
}

static inline void IrClassMemberVar_destroy(IrClassMemberVar* self)
{
    String_destroy(&self->name);
    String_destroy(&self->type);
}

typedef struct IrClass
{
    String name;
    List vars;
} IrClass;

static inline void IrClass_create(
    IrClass* self,
    const char* name
)
{
    assert(self);
    String_create(&self->name, 0, name);
    self->vars = EMPTY_LIST;
}

static inline void IrClass_destroy(IrClass* self)
{
    String_destroy(&self->name);
    List_destroy(&self->vars);
}

typedef struct IrFunction
{
    String name;
    IrClass class_in;
    IrClass class_out;
} IrFunction;

static inline void IrFunction_create(
    IrFunction* self,
    const char* name
)
{
    assert(self);
    String_create(&self->name, 0, name);
    IrClass_create(&self->class_in, "aaa");
    IrClass_create(&self->class_out, "bbb");
}

static inline void IrFunction_destroy(IrFunction* self)
{
    String_destroy(&self->name);
    IrClass_destroy(&self->class_in);
    IrClass_destroy(&self->class_out);
}


#endif // COH_IR_H_INCLUDED
