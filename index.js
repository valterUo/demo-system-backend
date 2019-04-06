const express = require('express')
const cmd = require('node-cmd')
const cors = require('cors')
const bodyParser = require('body-parser')
const app = express()
const processRef = cmd.get('sml snippets.sml')

app.use(cors())
app.use(bodyParser.json())

app.post('/ml', (request, response) => {
  let stream = processRef.stdout
  //console.log("Stream starting")
  processRef.stdin.write(request.body.command + "\n")
  stream.once('data', function (data) {
    //console.log("This is the data: ")
    //console.log(data)
    //console.log("Data ends, data sent.")
    response.send(data)
  })
})

const PORT = 3002
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`)
})