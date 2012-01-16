cfg=$config_dir
obj=$objdir
if [ -f "$cfg/$osname-pari.nsi" ]; then
  cp "$cfg/$osname-pari.nsi" "$obj/pari.nsi"
fi
