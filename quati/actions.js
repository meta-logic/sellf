/*
 * Giselle Reis
 * 08.2013
 */

// Because of Firefox's incompatibility with innerText
function setText(node, text) {
  if(node.innerText !== undefined) {
    node.innerText = text;
  }
  else {
    node.textContent = text;
  }
}

// Function that returns the XMLHTTP object
function getXMLHTTP() {
  try {
    return new XMLHttpRequest();
  } catch (e) {
    try {
      return new ActiveXObject("Microsoft.XMLHTTP");
    } catch (e) {
      return new ActiveXObject("Msxml2.XMLHTTP");
    }
  }
}

/*
 * actions:
 * - bipoles -> get the bipoles and rule names for the system
 *   params: system name
 * - permute -> check the permutation of rules
 *   params: system name, rule 1, rule 2
 *
 */

function genRules() {
  
  document.getElementById('result').style.display = 'none'
  document.getElementById('r1').value = ''
  document.getElementById('r2').value = ''

  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc
  
  var xmlhttp = getXMLHTTP() 

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('rules').style.display = 'block'
      setText(document.getElementById('rulesTex'), response)
      var math = document.getElementById("rulesTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }
  
  xmlhttp.open("POST", "rules.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)
  
  var xmlhttp2 = getXMLHTTP()

  // When the answer is received:
  xmlhttp2.onreadystatechange = function () {
    if(xmlhttp2.readyState == 4 && xmlhttp2.status == 200) {
      var response = xmlhttp2.responseText

      // Split the lines
      var rules = response.match(/[^\r\n]+/g);

      var menu1 = document.getElementById("r1")
      var menu2 = document.getElementById("r2")

      // Remove old options
      while (menu1.firstChild) {
        menu1.removeChild(menu1.firstChild);
        menu2.removeChild(menu2.firstChild);
      }

      // Each line generates an entry in the dropdown menu
      for (var i=0; i < rules.length; i++) {
        var option1 = document.createElement("option")
        option1.text = rules[i]
        option1.value = rules[i]
        menu1.add(option1)
        var option2 = document.createElement("option")
        option2.text = rules[i]
        option2.value = rules[i]
        menu2.add(option2)
      }

      // Enable permutation and bipoles tabs
      myJQ('#tabs').tabs("option", "disabled", [])

    }
  }

  xmlhttp2.open("POST", "ruleNames.py", true)
  xmlhttp2.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp2.send(params)

}

function genBipoles() {
  
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc
  
  var xmlhttp = getXMLHTTP() 

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('bipoles').style.display = 'block'
      setText(document.getElementById('bipolesTex'), response)
      var math = document.getElementById("bipolesTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }

  xmlhttp.open("POST", "bipoles.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)

}

function checkPermutation() {
  
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value

  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)

  var r1 = document.getElementById('r1').value
  var r2 = document.getElementById('r2').value

  var params = "src=" + src_enc + "&sig=" + sig_enc + "&r1=" + r1 + "&r2=" + r2

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      // MathJax rendering
      document.getElementById('result').style.display = 'block'
      setText(document.getElementById('permutationsTex'), response)
      var math = document.getElementById("permutationsTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }

  xmlhttp.open("POST", "permutation.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)

}

function getExample() {

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var str = xmlhttp.responseText
      var v = str.split("##EOF##", 2)
      document.getElementById("specification").value = v[0];
      document.getElementById("signature").value = v[1];
      //document.getElementById("result_text").value = "Results";
    }
  }
 
  var e = document.getElementById("select")
  var str = e.options[e.selectedIndex].value
  var query = "?example="+str
  xmlhttp.open("GET", "load.py"+query, true)
  xmlhttp.send()

}

function downloadTexRules() {

  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value

  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)

  var params = "src=" + src_enc + "&sig=" + sig_enc

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var str = xmlhttp.responseText;
      var fileName = 'rules.tex';
      // Download is enabled using FileSaver.js and Blob.js
      // Probably it won't work in all browsers
      var blob = new Blob([str], {type: "text/plain;charset=utf-8"});
      saveAs(blob, fileName);
    }
  }

  xmlhttp.open("POST", "downloadTexRules.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)

}

function downloadTexPermutation() {

  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value

  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)

  var r1 = document.getElementById('r1').value
  var r2 = document.getElementById('r2').value

  var params = "src=" + src_enc + "&sig=" + sig_enc + "&r1=" + r1 + "&r2=" + r2

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var str = xmlhttp.responseText;
      var fileName = 'permutation.tex';
      // Download is enabled using FileSaver.js and Blob.js
      // Probably it won't work in all browsers
      var blob = new Blob([str], {type: "text/plain;charset=utf-8"});
      saveAs(blob, fileName);
    }
  }

  xmlhttp.open("POST", "downloadTexPermutation.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)

}

function downloadTexBipoles() {

  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value

  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)

  var params = "src=" + src_enc + "&sig=" + sig_enc

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var str = xmlhttp.responseText;
      var fileName = 'bipoles.tex';
      // Download is enabled using FileSaver.js and Blob.js
      // Probably it won't work in all browsers
      var blob = new Blob([str], {type: "text/plain;charset=utf-8"});
      saveAs(blob, fileName);
    }
  }

  xmlhttp.open("POST", "downloadTexBipoles.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  xmlhttp.send(params)

}
