# switch to debugging c:
define clang
  tui enable
  set extended-prompt gmayer@clang (\w)>
  set tui border-mode standout
  set tui active-border-mode standout
  set tui border-kind acs
  layout src
  # to see assembly too:
  # layout split
  # set disassembly-flavor intel
end

# switch to debugging assembly-language:
define asm
  set extended-prompt gmayer@asm (\w)>
  set disassembly-flavor intel
  # tui reg general
  tui reg all
  set tui border-mode standout
  set tui active-border-mode standout
  set tui border-kind acs
  layout asm
  layout regs
end
