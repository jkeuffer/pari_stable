!include "MUI.nsh"
!define MUI_PRODUCT "PARI"
!define MUI_VERSION "2.2.7"

;--------------------------------
AutoCloseWindow false

OutFile "Pari.exe"
InstallDir "$PROGRAMFILES\PARI"
InstallDirRegKey HKLM "Software\PARI" ""
LicenseData "..\COPYING"

!define MUI_WELCOMEPAGE
!define MUI_LICENSEPAGE
!define MUI_COMPONENTSPAGE
!define MUI_DIRECTORYPAGE
!define MUI_ABORTWARNING
!define MUI_UNINSTALLER
!define MUI_UNCONFIRMPAGE
!insertmacro MUI_LANGUAGE "English"
;--------------------------------
;Installer Sections

!define uninst "Software\Microsoft\Windows\CurrentVersion\Uninstall\PARI"

Section "pari (required)" SecCopy
  SetOutPath "$INSTDIR"
  File /oname=gp.exe "..\Ocygwin-i686\gp-dyn.exe"
  File "makegprc"
  File "..\misc\tex2mail"
  File "..\Ocygwin-i686\libpari-2.2.dll"
  File "\cygwin\bin\cygwin1.dll"
  File "\cygwin\bin\cygncurses7.dll"
  File "\cygwin\bin\cygreadline5.dll"
  File "\cygwin\bin\cygperl5_8_0.dll"
  File "\cygwin\bin\perl.exe"

  WriteRegStr HKCU "Software\PARI" "" $INSTDIR
  WriteRegStr HKLM ${uninst} "DisplayName" "PARI (remove only)"
  WriteRegStr HKLM ${uninst} "UninstallString" '"$INSTDIR\uninstall.exe"'
  
  WriteUninstaller "$INSTDIR\Uninstall.exe"
SectionEnd

Section "Galois files" SecGAL
  SetOutPath "$INSTDIR\galdata"
  File "..\galdata\*"
SectionEnd

Section "documentation" SecDOC
  SetOutPath "$INSTDIR"
  File "..\doc\gphelp"
  SetOutPath $INSTDIR\doc
  File "..\doc\translations"
  File "..\doc\*.tex"
  File "..\doc\*.pdf"
SectionEnd

Function .onInstSuccess
  SetOutPath "$INSTDIR"
  ExecWait "perl makegprc $INSTDIR"
  Delete "$INSTDIR\makegprc"
  MessageBox MB_OK "Thanks for using PARI/GP! Double-click on 'gp' to start the calculator.$\r$\nTweak $INSTDIR\.gprc to customize GP (colors, script search path, etc.)."
  ExecShell "open" "$INSTDIR"
FunctionEnd

!define short "$SMPROGRAMS\PARI"
  
Section "shortcuts" SecSM
  CreateDirectory "${short}"
  CreateShortCut "${short}\gp.lnk" "$INSTDIR\gp.exe" "" "$INSTDIR\gp.exe" 0
  CreateShortCut "${short}\users.lnk" "$INSTDIR\doc\users.pdf" "" "$INSTDIR\doc\users.pdf" 0
  CreateShortCut "${short}\tutorial.lnk" "$INSTDIR\doc\tutorial.pdf" "" "$INSTDIR\doc\tutorial.pdf" 0
  CreateShortCut "${short}\refcard.lnk" "$INSTDIR\doc\refcard.pdf" "" "$INSTDIR\doc\refcard.pdf" 0
  WriteINIStr "${short}\PARI pages.url" "InternetShortcut" "URL" "http://www.math.u-psud.fr/~belabas/pari.html"
  CreateShortCut "${short}\Uninstall.lnk" "$INSTDIR\uninstall.exe" "" "$INSTDIR\uninstall.exe" 0
  CreateShortCut "$DESKTOP\PARI.lnk" "$INSTDIR\gp.exe"
SectionEnd

!insertmacro MUI_SECTIONS_FINISHHEADER

;--------------------------------
;Descriptions

LangString DESC_SecCopy ${LANG_ENGLISH} "Copy pari files to application folder."
LangString DESC_DOC ${LANG_ENGLISH} "Install documentation and online help."
LangString DESC_GAL ${LANG_ENGLISH} "Install Galois data files (degree > 7)."
LangString DESC_SM ${LANG_ENGLISH} "Add PARI shortcuts to Start Menu and desktop."

!insertmacro MUI_FUNCTIONS_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${SecCopy} $(DESC_SecCopy)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecGAL} $(DESC_GAL)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecSM} $(DESC_SM)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecDOC} $(DESC_DOC)
!insertmacro MUI_FUNCTIONS_DESCRIPTION_END
 
;--------------------------------
Section "Uninstall"
  Delete "$INSTDIR\gp.exe"
  Delete "$INSTDIR\.gprc"
  Delete "$INSTDIR\gphelp"
  Delete "$INSTDIR\tex2mail"
  Delete "$INSTDIR\libpari-2.2.dll"

  Delete "$INSTDIR\perl.exe"
  Delete "$INSTDIR\cygwin1.dll"
  Delete "$INSTDIR\cygncurses7.dll"
  Delete "$INSTDIR\cygreadline5.dll"
  Delete "$INSTDIR\Uninstall.exe"
  Delete "$INSTDIR\cygperl5_8_0.dll"
  RMDir /r "$INSTDIR\doc"
  RMDir /r "$INSTDIR\galdata"

  DeleteRegKey HKLM ${uninst}
  DeleteRegKey /ifempty HKLM "Software\PARI"

  RMDir /r "$SMPROGRAMS\PARI"
  Delete "$DESKTOP\PARI.lnk"
  RMDir "$INSTDIR"
  
  !insertmacro MUI_UNFINISHHEADER
SectionEnd
