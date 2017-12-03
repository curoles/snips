onerror {
  echo "On Error Tcl handler"
  quit -f -code 666
}

onbreak {
  echo "On Break Tcl handler"
  resume
}

onfinish stop

#assertion fail -action break Dve
#assertion action -cond pass -exec break Dve

run -all

echo "Exit simulation"
quit -f

