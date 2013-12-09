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

function genBipoles(sysName) {
  
  document.getElementById('result').style.display = 'none'
  document.getElementById('r1').value = ''
  document.getElementById('r2').value = ''
  
  var xmlhttp = getXMLHTTP() 

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('bipoles').style.display = 'block'
      setText(document.getElementById('bipolesTex'), "The bipoles for " + sysName + " are:\n" + response)
      var math = document.getElementById("bipolesTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }
 
  var query = "?system="+sysName
  xmlhttp.open("GET", "bipoles.py"+query, true)
  xmlhttp.send()
  
  var xmlhttp2 = getXMLHTTP()

  // When the answer is received:
  xmlhttp2.onreadystatechange = function () {
    if(xmlhttp2.readyState == 4 && xmlhttp2.status == 200) {
      var response = xmlhttp2.responseText
      
      // Split the lines
      var rules = response.match(/[^\r\n]+/g);

      var menu1 = document.getElementById("r1")
      var menu2 = document.getElementById("r2")
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
    }
  }
 
  xmlhttp2.open("GET", "ruleNames.py"+query, true)
  xmlhttp2.send()

}

function checkPermutation() {
  
  var system = document.getElementById('select').value
  var r1 = document.getElementById('r1').value
  var r2 = document.getElementById('r2').value

  if(r1 == '' || r2 == '') {
    alert("You must select the rules by typing their numbers in the boxes.")
    return
  }

  var xmlhttp = getXMLHTTP()

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('result').style.display = 'block'
      setText(document.getElementById('permutationsTex'), "The permutation of rules " + r1 + " and " + r2 + " of the system " + system + " are:\n" + response)
      var math = document.getElementById("permutationsTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }

  var query = "?system=" + system + "&r1=" + r1 + "&r2=" + r2
  xmlhttp.open("GET", "permutation.py"+query, true)
  xmlhttp.send()

}
