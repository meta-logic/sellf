#!/usr/bin/python

import cgi
import cgitb
import os
import urllib
from subprocess import Popen, PIPE

#show error messages on browser
cgitb.enable()

def submit():

  print "Content-type: text/html\n"
  
  form = cgi.FieldStorage()

  src_enc = form.getvalue('src')
  sig_enc = form.getvalue('sig')
  textAreaId_enc = form.getvalue('id')

  src = urllib.unquote(src_enc)
  sig = urllib.unquote(sig_enc)
  textAreaId = urllib.unquote(textAreaId_enc)

  src_file = open("files/spec_loadtex.pl", 'w')
  sig_file = open("files/spec_loadtex.sig", 'w')

  src_file.write(src)
  sig_file.write(sig)

  src_file.close()
  sig_file.close()

  cmdStr = ''
  fileName = ''

  if textAreaId == 'rulesSourceCode':
    cmdStr = './sellf -c rules_to_file -i files/spec_loadtex'
    fileName = 'rules.tex'
  elif textAreaId == 'permutationSourceCode':
    cmdStr = './sellf -c permute_to_file -i files/spec_loadtex'
    fileName = 'permutation.tex'
  elif textAreaId == 'bipolesSourceCode':
    cmdStr = './sellf -c bipoles_to_file -i files/spec_loadtex'
    fileName = 'bipoles.tex'

  # env attribute indicates where dlv.bin is located
  cmd = Popen(cmdStr, shell=True, stdout=PIPE, stderr=PIPE, env={'PATH': '/usr/local/bin'})
  stdout, stderr = cmd.communicate()

  os.remove("files/spec_loadtex.pl")
  os.remove("files/spec_loadtex.sig")

  result_file = open(fileName, 'r')

  result = result_file.read()

  result_file.close()

  os.remove(fileName)

  print result

submit()
