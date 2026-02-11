
get_tagged_union_info :: inline (T: Type, $ASSERT := false) -> *Type_Info_Struct {
    return get_tagged_union_info(T.(*Type_Info), ASSERT);
}

get_tagged_union_info :: inline (info: *Type_Info, $ASSERT := false) -> *Type_Info_Struct {
    info = get_variant_base_type(info);
    ifx is_tagged_union(info) then info;
    #if ASSERT then assert(info != null, "T must be a tagged union type.");
    return xx info;
}

get_tag_value_as_u64 :: (u: *$U) -> u64 {
    union_info := get_tagged_union_info(U, ASSERT = true);
    
    tag_member_info := *union_info.members[0];
    
    value_as_u64: u64;
    if tag_member_info.type.runtime_size == {
      case 1; value_as_u64 = xx,no_check u.(*u\8).*;
      case 2; value_as_u64 = xx,no_check u.(*u16).*;
      case 4; value_as_u64 = xx,no_check u.(*u32).*;
      case 8; value_as_u64 = xx,no_check u.(*u64).*;
    }
    return value_as_u64;
}

get_valid_member :: (u: *$U) -> Any {
    tag_value := get_tag_value_as_u64(u);
    union_info := type_info(U);
    for binding: union_info.tagged_union_bindings {
        if binding.constant_value == tag_value {
            valid_member_info := union_info.members[binding.member_index];
            return Any.{ valid_member_info.type, u.(*void) + valid_member_info.offset_in_bytes };
        }
    }
    assert(false, "Tag does not correspond to any valid union member.");
}

get_tag_value_for_union_member :: (union_type: *Type_Info, member_name: string) -> bool, u64 {
    union_info := get_tagged_union_info(union_type, ASSERT = true);
    
    tag_member_info := *union_info.members[0];
    
    for member_info, member_index: union_info.members {
        if member_info.flags & (.CONSTANT | .OVERLAY)  continue;
        if member_info.name == member_name {
            // Integer-tagged unions don't use tagged_union_bindings.
            if tag_member_info.type.type == .INTEGER {
                // TODO: We need to know how the compiler treats integer-tagged unions. This is not yet specified!
                //       For now I am assuming that we just use the member index, with no accounting for the tag or constant/overlay members.
                return true, xx,no_check member_index; 
            }
            
            for binding: union_info.tagged_union_bindings {
                if binding.member_index == xx member_index {
                    return true, binding.constant_value;
                }
            }
            log_error("Union member %.% does not have any binding.", union_info.name, member_name);
            return false, 0;
        }
    }
    log_error("'%' is not an assignable member of union type '%'.", member_name, union_info.name);
    return false, 0;
}

get_union_tag_type :: (U: Type) -> Type #compile_time {
    union_info := get_tagged_union_info(U, ASSERT = true);
    return get_type(union_info.members[0].type);
}

isa :: (u: *$U, $TAG_EXPRESSION: Code, $loc := #caller_location) -> *$R #modify {
    union_info := get_tagged_union_info(U);
    if union_info == null {
        return false, "U must be a tagged union type.";
    }
    
    tag_member_info := *union_info.members[0];
    if tag_member_info.type.type != .ENUM {
        return false, "U's tag type must be an enum.";
    }
    
    /*
        We have to manually typecheck the tag expression to get around limitations of #modify.
        It can be either an untyped unary-dot-identifier, or a fully qualified enum value with the type present.
    */
    tag_expression := compiler_get_nodes(TAG_EXPRESSION);
    
    tag_ident_node := is_unary_dot_ident(tag_expression);
    if tag_ident_node == null {
        if tag_expression.type != tag_member_info.type {
            return false, "Tag expression does not match union tag type.";
        }
        
        tag_ident_node = find_enum_value_ident_node(tag_expression);
        if tag_ident_node == null {
            return false, "Unable to determine enum value name from given tag expression.";
        }
    }
    
    tag_value_ok, tag_value := enum_name_to_value(tag_member_info.type, tag_ident_node.name);
    if !tag_value_ok {
        return false, "Unable to determine enum value from name.";
    }
    
    for binding: union_info.tagged_union_bindings {
        if binding.constant_value == xx tag_value {
            target_member_info := *union_info.members[binding.member_index];
            R = get_type(target_member_info.type);
            return true;
        }
    }
    return false, "No union member corresponds to given tag value.";
} #expand {
    TAG_TYPE :: #run get_union_tag_type(U);
    TAG_VALUE : TAG_TYPE : #insert TAG_EXPRESSION;
    #insert -> string {
        union_info := get_tagged_union_info(U, ASSERT = true);
        tag_member := *union_info.members[0];
        for binding: union_info.tagged_union_bindings {
            if binding.constant_value == xx TAG_VALUE {
                target_member := *union_info.members[binding.member_index];
                return tprint("return ifx u.%1 == TAG_VALUE then *u.%2;", tag_member.name, target_member.name);
            }
        }
        assert(false, "unreachable");
        return "";
    }
}

is_unary_dot_ident :: (code: *Code_Node) -> *Code_Ident {
    if code.kind == .UNARY_OPERATOR {
        code_unary_op := code.(*Code_Unary_Operator);
        if code_unary_op.operator_type == #char "."
        && code_unary_op.subexpression.kind == .IDENT {
            return xx code_unary_op.subexpression;
        }
    }
    return null;
}

find_enum_value_ident_node :: (node: *Code_Node) -> *Code_Ident {
    if node.kind == {
      case .IDENT;
        if node.type.type == .ENUM
        || node.type.type == .UNTYPED_ENUM {
            return xx node;
        }
        
      case .BINARY_OPERATOR;
        binop := node.(*Code_Binary_Operator);
        if binop.operator_type == #char "." {
            return find_enum_value_ident_node(binop.right);
        }
        
      case .UNARY_OPERATOR;
        unop := node.(*Code_Unary_Operator);
        if unop.operator_type == #char "." {
            return find_enum_value_ident_node(unop.subexpression);
        }
    }
    return null;
}

tag_of :: ($code: Code) -> $R #modify {
    // Check that the code provided is of the proper form, e.g.: `u.foo`
    // The cast to *Code_Binary_Operator here is checked by code_is_union_member_dereference.
    root := compiler_get_nodes(code).(*Code_Binary_Operator);
    if !code_is_union_member_dereference(root) return false, "Argument to tag_of() must be of the form 'union.member'.";
    
    // Set R to the union's tag type
    union_info := assert_base_type(root.left.type, .STRUCT);
    R = get_type(union_info.members[0].type);
    return true, "";
} #expand {
    TAG_VALUE :: #run -> R {
        // because we checked that the left and right types are as expected in the modify, we don't do any checking here.
        root          := compiler_get_nodes(code).(*Code_Binary_Operator);
        member_ident  := root.right.(*Code_Ident).name;
        ok, tag_value := get_tag_value_for_union_member(root.left.type, member_ident);
        
        assert(ok);
        return tag_value.(R);
    };
    return TAG_VALUE;
}

tag_of :: ($U: Type, $member_name: string) -> $R #modify {
    R = get_union_tag_type(U);
    return true;
} #expand {
    TAG_VALUE :: #run -> R {
        ok, tag_value := get_tag_value_for_union_member(xx U, member_name);
        assert(ok);
        return tag_value.(R);
    };
    return TAG_VALUE;
}

code_is_union_member_dereference :: (code: *Code_Node) -> bool #compile_time {
    root := code.(*Code_Binary_Operator);
    return root.kind == .BINARY_OPERATOR
        && root.operator_type == #char "."
        && root.right.kind == .IDENT
        && is_tagged_union(root.left.type);
}

is_valid :: ($code: Code) -> bool #modify {
    root := compiler_get_nodes(code);
    if !code_is_union_member_dereference(root) return false, "Argument to tag_of() must be of the form 'union.member'.";
    return true, "";
} #expand {
    // Insert code to compare the union tag to the expected value for the given member.
    // This will look like
    //      `return u.tag == <literal of tag type>;`
    // but the union and tag identifiers will depend on whatever the user passed as `code`.
    ok := #insert -> Code {
        // because we checked that the left and right types are as expected in the modify, we don't do any checking here.
        root := compiler_get_nodes(code).(*Code_Binary_Operator);
        member_ident := root.right.(*Code_Ident).name;
        
        union_info := get_variant_base_type(root.left.type).(*Type_Info_Struct);
        tag_member_info := *union_info.members[0];
        
        for union_info.members {
            if it.name == member_ident {
                compare := New(Code_Binary_Operator);
                compare.operator_type = .IS_EQUAL;
                
                // Copy LHS of `union.member` exression, replacing `member` with tag member's identifier.
                // This allows you to say things like `is_valid(some_struct.union.member)` and it still works.
                lhs := New(Code_Binary_Operator);
                lhs.operator_type = #char ".";
                lhs.left  = root.left;
                lhs.right = make_identifier(tag_member_info.name);
                
                ok, tag_value := get_tag_value_for_union_member(root.left.type, member_ident);
                assert(ok);
                
                compare.left  = lhs;
                compare.right = make_integer_literal(xx,no_check tag_value);
                
                return compiler_get_code(compare, code);
            }
        }
        
        assert(false, "'%' is not an assignable member of union type '%'", member_ident, get_type(union_info));
        return #code,null;
    };
    
    return ok;
}

// value_expression is also a Code for ease of implementation here, but maybe we should just make it a $T and work around that. I dunno.
set :: ($code: Code, $value_expression: Code, $loc := #caller_location) -> bool #modify {
    root := compiler_get_nodes(code);
    if !code_is_union_member_dereference(root) return false, "Argument to set() must be of the form 'union.member'.";
    return true, "";
} #expand {
    #insert -> Code {
        // because we checked that the left and right types are as expected in the modify, we don't do any checking here.
        root := compiler_get_nodes(code).(*Code_Binary_Operator);
        member_ident := root.right.(*Code_Ident).name;
        
        union_info := get_variant_base_type(root.left.type).(*Type_Info_Struct);
        tag_member_info := *union_info.members[0];
        
        // create a block so we can insert 2 statements
        // first  statement is tag    assignment
        // second statement is member assignment
        block := New(Code_Block);
        block.block_type = .IMPERATIVE;
        block.statements = NewArray(2, *Code_Node);
        
        // we create the second statement first because the control flow is simpler this way
        block.statements[1] = ifx 1 {
            assignment := New(Code_Binary_Operator);
            assignment.operator_type = #char "=";
            assignment.left = ifx 1 {
                dot := New(Code_Binary_Operator);
                dot.operator_type = #char ".";
                dot.left = ifx 1 {
                    ident := make_identifier(root.left.(*Code_Ident).name);
                    ident.flags = .HAS_SCOPE_MODIFIER;
                    ident;
                };
                dot.right = root.right;
                dot;
            };
            assignment.right = compiler_get_nodes(value_expression);
            assignment;
        };
        
        for union_info.members {
            if it.name == member_ident {
                assignment := New(Code_Binary_Operator);
                assignment.operator_type = #char "=";
                
                lhs := New(Code_Binary_Operator);
                lhs.operator_type = #char ".";
                lhs.left  = ifx 1 {
                    ident := make_identifier(root.left.(*Code_Ident).name);
                    ident.flags = .HAS_SCOPE_MODIFIER;
                    ident;
                };
                lhs.right = make_identifier(tag_member_info.name);
                
                ok, tag_value := get_tag_value_for_union_member(root.left.type, member_ident);
                assert(ok);
                
                assignment.left  = lhs;
                assignment.right = make_integer_literal(xx,no_check tag_value);
                
                block.statements[0] = assignment;
                
                return compiler_get_code(block);
            }
        }
        
        compiler_report(tprint("'%' is not an assignable member of union type '%'", member_ident, get_type(union_info)), loc = loc);
        return #code,null;
    };
}












/*
    `make` and `set` procedures were written by @Žick 
    
    
*/

make :: ($type: Type, tag: Code, value := #code,null, loc := #caller_location) -> type #expand {
    tu: type = ---;
    set(*tu, #insert tag, value, loc);
    return tu;
}

set :: (tu: *$T, $tag_code: Code, value_code := #code,null, loc := #caller_location) #expand {
    tag_type :: #insert -> string {
        info := type_info(T).(*Type_Info_Struct); // explicit cast so that we report our own error if not a struct instead of info.textual_flags not existing producing its own error before we can report ours...
        if info.type != .STRUCT
        || !(info.textual_flags & .UNION)
        || !(info.textual_flags & .UNION_IS_TAGGED)
        then compiler_report(tprint("Type $T must be a tagged union, but type % is not.", T), loc=loc);
        
        // for now the tag is always the first member of the tagged union. We use type_of instead of just printing
        // the type in case the tag type is anonymous.
        return tprint("type_of(tu.%);", info.members[0].name);
    };
    
    tag : tag_type : #insert tag_code;
    
    // the tag is the first member so doing this should be fine???
    tu.(*tag_type).* = tag;
    
    // we can't do a #modify here either, something about tag being a baked parameter with a type dependency
    member_pointer := #insert -> string {
        info := type_info(T);
        
        found := false;
        binding: Type_Info_Tagged_Union_Binding;
        for info.tagged_union_bindings if it.constant_value == xx tag {
            found   = true;
            binding = it;
            break;
        }
        
        if !found compiler_report(tprint("Tag % could not be found in the tagged_union_bindings of type %. This should never happen, because this should be typechecked when `tag : tag_type : #insert tag_code` is executed. Right?`", tag, T));
        
        member := info.members[binding.member_index];
        variant_type := get_type(member.type);
        status, value_type := get_root_type(value_code);
        
        if status == {
        case .SUCCESS; if value_type != variant_type
        then compiler_report(
            tprint("Tag % expects a value of type %, got %.", tag, variant_type, value_type),
            loc=loc
        );
        
        case .INPUT_IS_CODE_NULL; if variant_type != void
        then compiler_report(
            tprint("You can only omit value_code for variants of type void, tag % expects a value of type %.", tag, variant_type),
            loc=loc
        );
        
        case; compiler_report(
            tprint("Could not get the type of the value passed in, get_type returned %.", status),
            loc=loc
        );
        }
        
        return tprint("*tu.%;", member.name);
    };
    
    #if value_code then member_pointer.* = #insert value_code;
}


// TODO: Ideally, we should not be taking `u` as Code here. 
match :: ($u: Code, $matches: ..Code, $loc := #caller_location) #modify {
    status, union_info := get_root_type(u);
    if !is_tagged_union(union_info)  return false, "u must be a tagged union.";
    if union_info.(*Type_Info_Struct).members[0].type.type != .ENUM  return false, "Tagged union must have an enum tag type.";
    return true;
} #expand {
    // TODO: may not need scope redirection here if the lambda bodies have the proper scope on them.
    #insert,scope(u) -> Code {
        push_allocator(temp);
        auto_release_temp();
        
        union_expression := compiler_get_nodes(u);
        union_info := get_tagged_union_info(union_expression.type, ASSERT = true);
        
        union_tag_member_name := union_info.members[0].name;
        union_tag_enum_info := union_info.members[0].type.(*Type_Info_Enum);
        
        cases: [..] *Code_Case;
        
        for matches {
            header := compiler_get_nodes(it).(*Code_Procedure_Header);
            
            if !(header.kind == .PROCEDURE_HEADER && (header.procedure_flags & .QUICK == .QUICK)) {
                compiler_report("Expected a quick lambda expression for match case.", loc = get_location(header));
            }
            
            // For now, only allow one ident per case. Syntax would potentially allow for multiple though. We could use this for fallthrough cases...
            if (header.arguments.count != 1) {
                compiler_report("Quick lambda expression used as a match case must only accept one argument, representing the enum value of the union tag to match.", loc = get_location(header));
            }
            
            enum_value_name := header.arguments[0].(*Code_Declaration).name;
            is_default_case := enum_value_name == "_";
            
            code_case := New(Code_Case);
            
            assert(header.body_or_null != null);
            body_statements := header.body_or_null.block.statements;
            
            code_case.then_block = ifx 1 {
                block := New(Code_Block);
                
                block.block_type = .IMPERATIVE;
                block.owning_statement = code_case;
                
                // May be null if this is the default case or if the enum value does not have a binding to any union member.
                using_statement: *Code_Using;
                
                if !is_default_case {
                    code_case.condition = make_unary_operator(#char ".", make_identifier(enum_value_name));
                    
                    found, enum_integer_value := enum_name_to_value(union_tag_enum_info, enum_value_name);
                    if !found {
                        log("union tag enum info: %", union_tag_enum_info.*);
                        compiler_report(tprint("% is not a valid value of enum tag type.", enum_value_name), loc = get_location(header));
                    }
                    
                    for binding: union_info.tagged_union_bindings {
                        if binding.constant_value == xx,no_check enum_integer_value {
                            target_member_info := *union_info.members[binding.member_index];
                            
                            using_statement = ifx 1 {
                                root := New(Code_Using);
                                root.expression  = union_expression;
                                root.filter_type = .ONLY;
                                
                                // TODO: figure out how to simplify this so we don't need to use compiler_get_nodes
                                //       for some reason, we get an unresolved identifier error if we just use an ident for the member we want to `using`
                                //       so we have to do this string array thing as a workaround
                                filter_expression := compiler_get_nodes(string.[]).(*Code_Literal);
                                filter_expression.array_literal_info.array_members = array_copy((*Code_Node).[ make_string_literal(target_member_info.name) ]);
                                root.filter_expression = filter_expression;
                                
                                root;
                            };
                        }
                    }
                }
                
                if using_statement {
                    block.statements = NewArray(body_statements.count + 1, *Code_Node);
                    for body_statements  block.statements[it_index + 1] = it;
                    block.statements[0] = using_statement;
                } else {
                    block.statements = body_statements;
                }
                
                // remove the implicit return statement that gets inserted in quick lambdas
                return_statement := block.statements[block.statements.count-1].(*Code_Return);
                if return_statement.kind == .RETURN {
                    assert(return_statement.arguments_unsorted.count == 1);
                    block.statements[block.statements.count-1] = return_statement.arguments_unsorted[0].expression;
                }
                
                block;
            };
            
            array_add(*cases, code_case);
        }
        
        code_if := make_if_case(make_binary_operator(#char ".", union_expression, make_identifier(union_tag_member_name)), cases);
        
        // uncomment this to see what the final code would look like
        // #import "Program_Print";
        // sb: String_Builder;
        // print_expression(*sb, code_if);
        // write_string("----------------------------\n");
        // write_string(builder_to_string(*sb));
        // write_string("\n");
        
        return compiler_get_code(code_if);
    }
}
