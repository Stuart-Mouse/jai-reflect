




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
        union_info := assert_base_type(union_expression.type, .STRUCT);
        
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
                    
                    enum_integer_value, found := enum_name_to_value(union_tag_enum_info, enum_value_name);
                    if !found {
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
