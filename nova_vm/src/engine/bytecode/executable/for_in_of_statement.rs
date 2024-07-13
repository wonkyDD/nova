// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use super::{is_reference, CompileContext, CompileEvaluation, Instruction};
use crate::ecmascript::types::{String, Value};
use oxc_ast::{ast, syntax_directed_operations::BoundNames};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IterationKind {
    Enumerate,
    Iterate,
    AsyncIterate,
}

#[derive(Debug, PartialEq, Eq)]
enum LeftHandSideKind {
    Assignment,
    VarBinding,
    LexicalBinding,
}

#[derive(Debug, PartialEq, Eq)]
enum IteratorKind {
    Sync,
    Async,
}

fn for_in_of_head_evaluation(
    ctx: &mut CompileContext,
    uninitialized_bound_names: Vec<String>,
    expr: &ast::Expression<'_>,
    iteration_kind: IterationKind,
) {
    // 1. Let oldEnv be the running execution context's LexicalEnvironment.
    // 2. If uninitializedBoundNames is not empty, then
    if !uninitialized_bound_names.is_empty() {
        // a. Assert: uninitializedBoundNames has no duplicate entries.
        // b. Let newEnv be NewDeclarativeEnvironment(oldEnv).
        ctx.exe
            .add_instruction(Instruction::EnterDeclarativeEnvironment);
        // c. For each String name of uninitializedBoundNames, do
        for name in uninitialized_bound_names.iter() {
            // i. Perform ! newEnv.CreateMutableBinding(name, false).
            ctx.exe
                .add_instruction_with_identifier(Instruction::CreateMutableBinding, *name);
        }
        // d. Set the running execution context's LexicalEnvironment to newEnv.
    }
    // 3. Let exprRef be Completion(Evaluation of expr).
    expr.compile(ctx);
    // 4. Set the running execution context's LexicalEnvironment to oldEnv.
    if !uninitialized_bound_names.is_empty() {
        ctx.exe
            .add_instruction(Instruction::ExitDeclarativeEnvironment);
    }
    // 5. Let exprValue be ? GetValue(? exprRef).
    if is_reference(expr) {
        ctx.exe.add_instruction(Instruction::GetValue);
    }
    // 6. If iterationKind is ENUMERATE, then
    match iteration_kind {
        IterationKind::Enumerate => {
            // a. If exprValue is either undefined or null, then
            // Add a copy to stack.
            ctx.exe.add_instruction(Instruction::LoadCopy);
            ctx.exe.add_instruction(Instruction::IsNullOrUndefined);
            let jump_over_undefined_or_null = ctx
                .exe
                .add_instruction_with_jump_slot(Instruction::JumpIfNot);
            // i. Return Completion Record { [[Type]]: BREAK, [[Value]]: EMPTY, [[Target]]: EMPTY }.
            // Remove the copy added above.
            ctx.exe.add_instruction(Instruction::Store);
            ctx.exe
                .add_instruction_with_constant(Instruction::StoreConstant, Value::Undefined);
            let jump_to_end_from_undefined_or_null =
                ctx.exe.add_instruction_with_jump_slot(Instruction::Jump);
            ctx.current_break
                .as_mut()
                .unwrap()
                .push(jump_to_end_from_undefined_or_null);
            ctx.exe.set_jump_target_here(jump_over_undefined_or_null);
            // Load back the copy from above.
            ctx.exe.add_instruction(Instruction::Store);
            // b. Let obj be ! ToObject(exprValue).
            // c. Let iterator be EnumerateObjectProperties(obj).
            // d. Let nextMethod be ! GetV(iterator, "next").
            // e. Return the Iterator Record { [[Iterator]]: iterator, [[NextMethod]]: nextMethod, [[Done]]: false }.
            ctx.exe
                .add_instruction(Instruction::EnumerateObjectProperties);
            // Note: iteratorKind is SYNC
        }
        // 7. Else,
        // a. Assert: iterationKind is either ITERATE or ASYNC-ITERATE.
        IterationKind::AsyncIterate => {
            // b. If iterationKind is ASYNC-ITERATE, let iteratorKind be ASYNC.
            // d. Return ? GetIterator(exprValue, iteratorKind).
            ctx.exe.add_instruction(Instruction::GetIteratorAsync);
        }
        IterationKind::Iterate => {
            // c. Else, let iteratorKind be SYNC.
            // d. Return ? GetIterator(exprValue, iteratorKind).
            ctx.exe.add_instruction(Instruction::GetIteratorSync);
        }
    }
}

enum AssignmentPattern<'a> {
    ArrayAssignmentTarget(&'a ast::ArrayAssignmentTarget<'a>),
    ObjectAssignmentTarget(&'a ast::ObjectAssignmentTarget<'a>),
}

fn for_in_of_body_evaluation(
    ctx: &mut CompileContext,
    lhs: &ast::ForStatementLeft<'_>,
    stmt: &ast::Statement<'_>,
    _iteration_kind: IterationKind,
    lhs_kind: LeftHandSideKind,
    _label_set: (),
    _iterator_kind: Option<IteratorKind>,
) {
    // 1. If iteratorKind is not present, set iteratorKind to SYNC.
    let _iterator_kind = _iterator_kind.unwrap_or(IteratorKind::Sync);
    // 2. Let oldEnv be the running execution context's LexicalEnvironment.
    // 3. Let V be undefined.
    ctx.exe
        .add_instruction_with_constant(Instruction::StoreConstant, Value::Undefined);
    // 4. Let destructuring be IsDestructuring of lhs.
    let destructuring = if let ast::ForStatementLeft::VariableDeclaration(lhs) = lhs {
        assert_eq!(lhs.declarations.len(), 1);
        lhs.declarations[0].id.kind.is_destructuring_pattern()
    } else {
        lhs.is_assignment_target_pattern()
    };
    // 5. If destructuring is true and lhsKind is ASSIGNMENT, then
    let _assignment_pattern = if destructuring && lhs_kind == LeftHandSideKind::Assignment {
        // a. Assert: lhs is a LeftHandSideExpression.
        // b. Let assignmentPattern be the AssignmentPattern that is covered by lhs.
        Some(match lhs {
            ast::ForStatementLeft::ArrayAssignmentTarget(lhs) => {
                AssignmentPattern::ArrayAssignmentTarget(lhs)
            }
            ast::ForStatementLeft::ObjectAssignmentTarget(lhs) => {
                AssignmentPattern::ObjectAssignmentTarget(lhs)
            }
            _ => unreachable!(),
        })
    } else {
        None
    };
    // 6. Repeat,
    let repeat_jump = ctx.exe.get_jump_index_to_here();
    // a. Let nextResult be ? Call(iteratorRecord.[[NextMethod]], iteratorRecord.[[Iterator]]).
    // b. If iteratorKind is ASYNC, set nextResult to ? Await(nextResult).
    // c. If nextResult is not an Object, throw a TypeError exception.
    ctx.exe.add_instruction(Instruction::IteratorNext);

    // d. Let done be ? IteratorComplete(nextResult).
    // e. If done is true, return V.
    let jump_to_end = ctx
        .exe
        .add_instruction_with_jump_slot(Instruction::IteratorComplete);
    ctx.current_break.as_mut().unwrap().push(jump_to_end);
    // f. Let nextValue be ? IteratorValue(nextResult).
    ctx.exe.add_instruction(Instruction::IteratorValue);
    let mut entered_declarative_environment = false;
    // g. If lhsKind is either ASSIGNMENT or VAR-BINDING, then
    match lhs_kind {
        LeftHandSideKind::Assignment | LeftHandSideKind::VarBinding => {
            // i. If destructuring is true, then
            if destructuring {
                // 1. If lhsKind is ASSIGNMENT, then
                if lhs_kind == LeftHandSideKind::Assignment {
                    // a. Let status be Completion(DestructuringAssignmentEvaluation of assignmentPattern with argument nextValue).
                    todo!();
                } else {
                    // 2. Else,
                    // a. Assert: lhsKind is VAR-BINDING.
                    // b. Assert: lhs is a ForBinding.
                    // c. Let status be Completion(BindingInitialization of lhs with arguments nextValue and undefined).
                    todo!();
                }
            } else {
                // ii. Else,
                // 1. Let lhsRef be Completion(Evaluation of lhs). (It may be evaluated repeatedly.)
                match lhs {
                    ast::ForStatementLeft::VariableDeclaration(decl) => {
                        assert_eq!(decl.declarations.len(), 1);
                        let declaration = decl.declarations.first().unwrap();
                        match &declaration.id.kind {
                            ast::BindingPatternKind::BindingIdentifier(binding_identifier) => {
                                let identifier =
                                    String::from_str(ctx.agent, binding_identifier.name.as_str());
                                ctx.exe.add_instruction_with_identifier(
                                    Instruction::ResolveBinding,
                                    identifier,
                                );
                            }
                            ast::BindingPatternKind::AssignmentPattern(_)
                            | ast::BindingPatternKind::ObjectPattern(_)
                            | ast::BindingPatternKind::ArrayPattern(_) => unreachable!(),
                        }
                    }
                    ast::ForStatementLeft::AssignmentTargetIdentifier(identifier_reference) => {
                        let identifier =
                            String::from_str(ctx.agent, identifier_reference.name.as_str());
                        ctx.exe.add_instruction_with_identifier(
                            Instruction::ResolveBinding,
                            identifier,
                        );
                    }
                    _ => unreachable!(),
                }

                // 2. If lhsRef is an abrupt completion, then
                // a. Let status be lhsRef.
                // 3. Else,
                // a. Let status be Completion(PutValue(lhsRef.[[Value]], nextValue)).
                ctx.exe.add_instruction(Instruction::PutValue);
            }
        }
        LeftHandSideKind::LexicalBinding => {
            // h. Else,
            // i. Assert: lhsKind is LEXICAL-BINDING.
            // ii. Assert: lhs is a ForDeclaration.
            let ast::ForStatementLeft::VariableDeclaration(lhs) = lhs else {
                unreachable!()
            };
            // iii. Let iterationEnv be NewDeclarativeEnvironment(oldEnv).
            ctx.exe
                .add_instruction(Instruction::EnterDeclarativeEnvironment);
            entered_declarative_environment = true;
            // iv. Perform ForDeclarationBindingInstantiation of lhs with argument iterationEnv.
            lhs.bound_names(&mut |binding_identifier| {
                let identifier = String::from_str(ctx.agent, binding_identifier.name.as_str());
                ctx.exe.add_instruction_with_identifier(
                    if lhs.kind.is_const() {
                        Instruction::CreateImmutableBinding
                    } else {
                        Instruction::CreateMutableBinding
                    },
                    identifier,
                );
            });
            // v. Set the running execution context's LexicalEnvironment to iterationEnv.
            // vi. If destructuring is true, then
            if destructuring {
                // 1. Let status be Completion(ForDeclarationBindingInitialization of lhs with arguments nextValue and iterationEnv).
                todo!();
            } else {
                // vii. Else,
                // 1. Assert: lhs binds a single name.
                let mut bound = false;
                lhs.bound_names(&mut |binding_identifier| {
                    assert!(!bound);
                    bound = true;
                    // 2. Let lhsName be the sole element of the BoundNames of lhs.
                    let lhs_name = String::from_str(ctx.agent, binding_identifier.name.as_str());
                    // 3. Let lhsRef be ! ResolveBinding(lhsName).
                    ctx.exe
                        .add_instruction_with_identifier(Instruction::ResolveBinding, lhs_name);
                    // 4. Let status be Completion(InitializeReferencedBinding(lhsRef, nextValue)).
                    ctx.exe
                        .add_instruction(Instruction::InitializeReferencedBinding)
                });
            }
        }
    }
    // TODO: How to do abrupt completion?
    // i. If status is an abrupt completion, then
    //      i. Set the running execution context's LexicalEnvironment to oldEnv.
    //      ii. If iteratorKind is ASYNC, return ? AsyncIteratorClose(iteratorRecord, status).
    //      iii. If iterationKind is ENUMERATE, then
    //      1. Return ? status.
    //      iv. Else,
    //      1. Assert: iterationKind is ITERATE.
    //      2. Return ? IteratorClose(iteratorRecord, status).

    // j. Let result be Completion(Evaluation of stmt).
    stmt.compile(ctx);

    // k. Set the running execution context's LexicalEnvironment to oldEnv.
    if entered_declarative_environment {
        ctx.exe
            .add_instruction(Instruction::ExitDeclarativeEnvironment);
    }
    let own_continues = ctx.current_continue.take().unwrap();
    for continue_entry in own_continues {
        ctx.exe.set_jump_target(continue_entry, repeat_jump.clone());
    }
    // TODO: Load V back from stack and compare with result, store.
    ctx.exe
        .add_jump_instruction_to_index(Instruction::Jump, repeat_jump);
    // l. If LoopContinues(result, labelSet) is false, then
    let own_breaks = ctx.current_break.take().unwrap();
    for break_entry in own_breaks {
        ctx.exe.set_jump_target_here(break_entry);
    }
    // i. If iterationKind is ENUMERATE, then
    // 1. Return ? UpdateEmpty(result, V).
    // ii. Else,
    // 1. Assert: iterationKind is ITERATE.
    // 2. Set status to Completion(UpdateEmpty(result, V)).
    // 3. If iteratorKind is ASYNC, return ? AsyncIteratorClose(iteratorRecord, status).
    // 4. Return ? IteratorClose(iteratorRecord, status).
    // m. If result.[[Value]] is not EMPTY, set V to result.[[Value]].
}

impl CompileEvaluation for ast::ForInStatement<'_> {
    fn compile(&self, ctx: &mut CompileContext) {
        let previous_continue = ctx.current_continue.replace(vec![]);
        let previous_break = ctx.current_break.replace(vec![]);

        let mut uninitialized_bound_names = vec![];

        let lhs_kind = match &self.left {
            ast::ForStatementLeft::VariableDeclaration(var_decl) => {
                if var_decl.kind.is_lexical() {
                    var_decl.bound_names(&mut |binding_identifier| {
                        uninitialized_bound_names.push(String::from_str(
                            ctx.agent,
                            binding_identifier.name.as_str(),
                        ));
                    });
                    LeftHandSideKind::LexicalBinding
                } else {
                    LeftHandSideKind::VarBinding
                }
            }
            ast::ForStatementLeft::ArrayAssignmentTarget(_)
            | ast::ForStatementLeft::AssignmentTargetIdentifier(_)
            | ast::ForStatementLeft::ComputedMemberExpression(_)
            | ast::ForStatementLeft::ObjectAssignmentTarget(_)
            | ast::ForStatementLeft::PrivateFieldExpression(_)
            | ast::ForStatementLeft::StaticMemberExpression(_) => LeftHandSideKind::Assignment,
            ast::ForStatementLeft::UsingDeclaration(_) => todo!(),
            ast::ForStatementLeft::TSAsExpression(_)
            | ast::ForStatementLeft::TSInstantiationExpression(_)
            | ast::ForStatementLeft::TSNonNullExpression(_)
            | ast::ForStatementLeft::TSSatisfiesExpression(_)
            | ast::ForStatementLeft::TSTypeAssertion(_) => unreachable!(),
        };

        for_in_of_head_evaluation(
            ctx,
            uninitialized_bound_names,
            &self.right,
            IterationKind::Enumerate,
        );
        for_in_of_body_evaluation(
            ctx,
            &self.left,
            &self.body,
            IterationKind::Enumerate,
            lhs_kind,
            (),
            None,
        );

        ctx.current_break = previous_break;
        ctx.current_continue = previous_continue;
    }
}

impl CompileEvaluation for ast::ForOfStatement<'_> {
    fn compile(&self, ctx: &mut CompileContext) {
        let previous_continue = ctx.current_continue.replace(vec![]);
        let previous_break = ctx.current_break.replace(vec![]);

        let mut uninitialized_bound_names = vec![];

        let lhs_kind = match &self.left {
            ast::ForStatementLeft::VariableDeclaration(var_decl) => {
                if var_decl.kind.is_lexical() {
                    var_decl.bound_names(&mut |binding_identifier| {
                        uninitialized_bound_names.push(String::from_str(
                            ctx.agent,
                            binding_identifier.name.as_str(),
                        ));
                    });
                    LeftHandSideKind::LexicalBinding
                } else {
                    LeftHandSideKind::VarBinding
                }
            }
            ast::ForStatementLeft::ArrayAssignmentTarget(_)
            | ast::ForStatementLeft::AssignmentTargetIdentifier(_)
            | ast::ForStatementLeft::ComputedMemberExpression(_)
            | ast::ForStatementLeft::ObjectAssignmentTarget(_)
            | ast::ForStatementLeft::PrivateFieldExpression(_)
            | ast::ForStatementLeft::StaticMemberExpression(_) => LeftHandSideKind::Assignment,
            ast::ForStatementLeft::UsingDeclaration(_) => todo!(),
            ast::ForStatementLeft::TSAsExpression(_)
            | ast::ForStatementLeft::TSInstantiationExpression(_)
            | ast::ForStatementLeft::TSNonNullExpression(_)
            | ast::ForStatementLeft::TSSatisfiesExpression(_)
            | ast::ForStatementLeft::TSTypeAssertion(_) => unreachable!(),
        };

        let (iteration_kind, iterator_kind) = if self.r#await {
            (IterationKind::AsyncIterate, Some(IteratorKind::Async))
        } else {
            (IterationKind::Iterate, None)
        };

        for_in_of_head_evaluation(ctx, uninitialized_bound_names, &self.right, iteration_kind);
        for_in_of_body_evaluation(
            ctx,
            &self.left,
            &self.body,
            iteration_kind,
            lhs_kind,
            (),
            iterator_kind,
        );

        ctx.current_break = previous_break;
        ctx.current_continue = previous_continue;
    }
}
