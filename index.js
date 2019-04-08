const express = require('express')
const formidable = require('formidable')
const fs = require('fs')
const cmd = require('node-cmd')
const cors = require('cors')
const bodyParser = require('body-parser')
const app = express()
let processRef
app.use(cors())
app.use(bodyParser.text())

app.post('/files', (request, response) => {
  fs.writeFile(request.get('FileName'), request.body, (err) => { 
     console.log(err)
     processRef = cmd.get('sml ' + request.get('FileName'))
     response.send("File created and process started.")
   })
 })

app.post('/ml', (request, response) => {
  if(processRef === undefined) {
    response.status(400).send({ error: "The ML file has not been defined." });
  } else {
  console.log("here")
  let stream = processRef.stdout
  //console.log("Stream starting")
  console.log(request.body)
  processRef.stdin.write(request.body + "\n")
  stream.once('data', function (data) {
    //console.log("This is the data: ")
    console.log(data)
    //console.log("Data ends, data sent.")
    response.send(data)
  })
}
})

const PORT = 3001
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`)
})