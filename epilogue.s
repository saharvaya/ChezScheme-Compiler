;; Start epilogue here
%define TRUE 1
%define FALSE 0

%macro PRINT 1
   xor rax, rax
   mov rdi, %1
   call printf
%endmacro

%macro RETURN_TRUE 1
   mov rax, TRUE
   jmp %1
%endmacro

%macro RETURN_FALSE 1
   mov rax, FALSE
   jmp %1
%endmacro

%macro LAST_ARG 1
   mov %1, ARG_COUNT
   dec %1
   mov %1, ARG_AT(%1)  ; get argument at param count - 1 -> arg[param_count - 1] = last argument
%endmacro

%define FIRST_ARG ARG_AT(0)

%define SECOND_ARG ARG_AT(1)

%define PUSH_RETURN push qword [rbp+WORD_SIZE*1]

%define PUSH_RBP push qword [rbp]

%macro CHECK_ARG_COUNT 1
   mov rbx, ARG_COUNT
   cmp rbx, qword %1
   jne param_count_error_exit
%endmacro


car:
    enter 0, 0

    CHECK_ARG_COUNT 1    ; car accepts 1 param only
    mov rcx, FIRST_ARG
    cmp SOB_TYPE(rcx), T_PAIR
    push car_exception
    jne pair_op_error_exit
    CAR rax, rcx

    leave
    ret


set_car:
   enter 0, 0

   CHECK_ARG_COUNT 2          ; set-car! accepts 2 params only
   mov rcx, FIRST_ARG         ; rcx will contain proper or improper list to replace car in
   mov rdx, SECOND_ARG        ; rdx will cointain the value to replace the car with
   cmp SOB_TYPE(rcx), T_PAIR  ; check if rcx is pair, proper list or improper list
   push set_car_exception
   jne pair_op_error_exit
   POINTER_FIRST rax, rcx    ; rax will now contain current car
   mov [rax], rdx            ; replace the SOB pointed by car of the pair to the SOB pointed by rdx
   RETURN_SOB_VOID           ; return void after operation

   leave
   ret


cdr:
  enter 0, 0

  CHECK_ARG_COUNT 1      ; cdr accepts 1 param only
  mov rcx, FIRST_ARG
  cmp SOB_TYPE(rcx), T_PAIR
  push cdr_exception
  jne pair_op_error_exit
  CDR rax, rcx

  leave
  ret


set_cdr:
  enter 0, 0

  CHECK_ARG_COUNT 2          ; set-cdr! accepts 2 params only
  mov rcx, FIRST_ARG         ; rcx will contain proper or improper list to replace cdr in
  mov rdx, SECOND_ARG        ; rdx will cointain the value to replace the cdr with
  cmp SOB_TYPE(rcx), T_PAIR  ; check if rcx is pair, proper list or improper list
  push set_cdr_exception
  jne pair_op_error_exit
  POINTER_SECOND rax, rcx    ; rax will now contain current cdr
  mov [rax], rdx             ; replace the SOB pointed by cdr of the pair to the SOB pointed by rdx
  RETURN_SOB_VOID            ; return void after operation

  leave
  ret


pair_op_error_exit:
    pop rdi          ; rdi contains exception message for pair operation failed
    push rcx         ; store SOB pointer
    PRINT rdi
    pop rsi
    call write_sob   ; print sob
    PRINT pair_error_msg
    mov rdi, -1      ; error code-1
    call exit


cons:
   enter 0, 0

   CHECK_ARG_COUNT 2  ; cons accepts 2 params only
   mov rbx, FIRST_ARG   ; rbx will point the car of the created pair
   mov rdx, SECOND_ARG  ; rdx will point the cdr of the created pair
   MAKE_PAIR(rax, rbx, rdx)

   leave
   ret

section .data
; Pair operations exception strings
car_exception: db `Exception in car: \0`
set_car_exception: db `Exception in set-car!: \0`
cdr_exception: db `Exception in cdr: \0`
set_cdr_exception: db `Exception in set-cdr!: \0`
pair_error_msg: db ` is not a pair\n\0`


apply:
   enter 0, 0

   mov rbx, ARG_COUNT
   cmp rbx, qword 1              ; apply accepts 2 or more arguments (first is procedure)
   jg .apply_sufficient_args
   push .apply_arg_exception     ; insufficient arguments passed, print exception
   push rbx
   jmp .apply_op_error_exit

.apply_sufficient_args:
   mov rcx, FIRST_ARG               ; expected procedure to apply
   cmp SOB_TYPE(rcx), T_CLOSURE     ; check if first procedure has type closure
   je .check_last_arg_validity
   PRINT .apply_no_closure_exception   ; first argument provided has no type closure, print exception
   mov rsi, FIRST_ARG
   call write_sob
   PRINT newline
   jmp .apply_exit_error

.check_last_arg_validity:
   dec rbx                ; rbx = param count passed to apply, ignore procedure
   mov rdx, ARG_AT(rbx)   ; rdx will contain the last argument passed to apply, should be a proper list

   .check_last_arg_is_proper_list:        ; check that last argument passed to apply is a proper list
      cmp SOB_TYPE(rdx), T_NIL   ; check if the last argument is nil which is a proper list
      jne .check_if_pair
      RETURN_TRUE .apply_valid_last_arg
   .check_if_pair:
      cmp SOB_TYPE(rdx), T_PAIR           ; check if last argument has type pair
      je .check_if_proper_list_cdr       ; if last argument has type pair, check that the cdr is a proper list
      RETURN_FALSE .apply_valid_last_arg
   .check_if_proper_list_cdr:
      CDR rdx, rdx               ; continue iterating on cdr to check if it is a proper list
      jmp .check_last_arg_is_proper_list

.apply_valid_last_arg:
   cmp rax, TRUE              ; check that the validity check for last argument as proper list returned true
   je .perform_apply          ; if arg count and last argument validity passed, can perform apply procedure
   PRINT .apply_exception     ; if last arg validity check returned false, print exception
   LAST_ARG rsi
   call write_sob
   PRINT .apply_not_proper_list_exception
   jmp .apply_exit_error

.perform_apply:
   ;; Calculate the total arguments we will pass to given procedure (first argument)
   LAST_ARG r9                   ; r9 = last argument passed, proper list argument passed to apply
   mov rcx, ARG_COUNT            ; rcx = arg count passed
   sub rcx, 2                    ; rcx = arg count - 2, arg count except the procedure and the last proper list arg
   call .apply_proper_lst_length ; rax will contain the length of passed proper list
   add rax, rcx                  ; rax = arg count-2 + length(proper list) = total arguments passed to apply including list except procedure
   ;; Prepare stack for apply
   PUSH_MAGIC
   ;; Push arguemnts given in proper list and out side of proper list
   mov rsi, rax                  ; rsi = all args count
   shl rsi, 3                    ; rsi = rdx * 8, amount of bytes = number of bytes to shift stack pointer
   sub rsp, rsi                  ; move stack pointer to make room for all apply arguments
   xor rdi, rdi                  ; rdi = 0
   mov rbx, 1                    ; rbx = 1, index of current argument (start after procedure, index 1)
   .store_arguments:             ; store arguemnts passed outside of the proper list on new stack position
   cmp rdi, rcx                  ; check finished moving args (except list and proc) to new stack position, rdi == arg count - 2
   je .store_arguments_end
   mov r10, ARG_AT(rbx)          ; get current iterated argument
   mov qword [rsp], r10          ; put argument on appropriate location on stack
   add rsp, WORD_SIZE            ; move stack pointer to next location to assign argument in
   inc rbx                       ; increment indices
   inc rdi
   jmp .store_arguments
   .store_arguments_end:
   mov rdi, r9                      ; rdi = proper list, last argument
   .store_list_arguments:
   cmp SOB_TYPE(rdi), T_NIL         ; check if finished iterating all proper list arguments
   je .store_list_arguments_end
   CAR r10, rdi                     ; r10 = current proper list car
   mov qword [rsp], r10             ; store current proper list argument (car) in next stack position
   add rsp, WORD_SIZE               ; move stack pointer to next position to assign to
   CDR rdi, rdi
   jmp .store_list_arguments
   .store_list_arguments_end:
   ;; Push new total arguemnt count, lexical enviorment, return address and rbp
   sub rsp, rsi                     ; return stack pointer to point to arg[0] (in the new arguments position) after copying arguments
   mov r12, rax                     ; r12 = total number of arguments including last arg proper list
   push rax                         ; push total argument count (in and out of the proper list) to stack
   mov rax, FIRST_ARG               ; rax = procedure passed to apply
   CLOSURE_ENV rbx, rax             ; rbx = lexical enviorment pointed by passed procedure
   push rbx                         ; push lexical enviorment to stack
   PUSH_RETURN                      ; push previous return address to stack
   PUSH_RBP                         ; push old rbp to stack
   CLOSURE_CODE rax, rax            ; rax points to given procedure closure code
   add r12, INIT_STACK_FRAME_SIZE   ; r12 = new stack frame size = total argument count + initial stack frame size -> r12 = total args + 5

   ;; Shift the new stack frame to override the old stack frame (the apply call stack frame)
   push rax                         ; store the pointer to closure code to be executed after shift on stack
   mov rax, INIT_STACK_FRAME_SIZE   ; rax = 5, initial stack frame size
   add rax, ARG_COUNT               ; rax = old stack frame size = init stack frame size + argument count
   mov rsi, rax
   shl rsi, 3                       ; rsi = rax, will contain the amount of bytes that the stack will be shfted
   mov rbx, 1                       ; j = rbx = current index in new stack frame
   mov rcx, r12                     ; i = rcx = r12, loop counter, initiated with the size of the new stack frame
   ;; Override the stack frame from the new stack frame to the old stack frame
   .apply_shift_frame:
      dec rax                             ; k = rax = rax - 1, index in old stack frame. initialy contains the old stack frame size
      neg rbx                             ; neg(rbx = j) => rbx = -j
      mov r8, qword [rbp+WORD_SIZE*rbx]   ; r8 = [rbp+8*(-j)] =[rbp-8*j]
      mov qword [rbp+WORD_SIZE*rax], r8   ; [rbp+8*k] = [rbp-8*j], override old stack frame current place with the corresponding place from the new stack frame
      neg rbx                             ; neg(rbx = -j) => rbx = j
      inc rbx                             ; rbx = j + 1
      loop .apply_shift_frame             ; rcx -= 1, i -= 1

   pop rax                           ; restore the pointer to closure code we pushed to stack before loop
   add rsp, rsi                      ; fix stack to point to the correct stack position after shift (old rbp)
   pop rbp                           ; rbp = old rbp
   jmp rax                           ; stack frame shifted to fixed location, can execute given procedure code


.apply_proper_lst_length:
   enter 0, 0

   mov rbx, r9       ; rbx = r9 which contains the proper list
   xor rax, rax      ; length of proper list will be returned in rax
   .get_length:
      cmp SOB_TYPE(rbx), T_NIL   ; if reached nil, finished iterating list
      jne .iterate_cdr
      leave
      ret
      .iterate_cdr:
      inc rax        ; increase list length counter
      CDR rbx, rbx   ; iteratre on list cdr
      jmp .get_length


.apply_op_error_exit:
   pop rsi
   pop rdi
   PRINT rdi
   jmp .apply_exit_error

.apply_exit_error:
   mov rdi, -1
   call exit

section .data
; Apply operation exception strings
.apply_arg_exception: db `Exception: incorrect argument count in call, apply accepts 2 or more arguments, got: %d\n\0`
.apply_no_closure_exception: db `Exception: attempt to apply non-procedure \0`
.apply_exception: db `Exception in apply: \0`
.apply_not_proper_list_exception: db ` is not a proper list\n\0`
newline: db `\n\0`
