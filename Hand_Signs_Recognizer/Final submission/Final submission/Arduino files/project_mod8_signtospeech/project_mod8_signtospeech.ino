#include <Arduino.h>
#include <TinyMLShield.h>
#include <TensorFlowLite.h>
#include <tensorflow/lite/micro/all_ops_resolver.h>
#include <tensorflow/lite/micro/micro_error_reporter.h>
#include <tensorflow/lite/micro/micro_interpreter.h>
#include <tensorflow/lite/schema/schema_generated.h>
#include <tensorflow/lite/version.h>
#include "model_data.h"
#include <ArduinoBLE.h>

const int image_width = 32;
const int image_height = 32;
const int num_channels = 1;
const int kTensorArenaSize = 50000;

bool captureFlag = false;
byte image[176 * 144 * 2];
int bytesPerFrame;

namespace {
  tflite::MicroErrorReporter micro_error_reporter;
  tflite::ErrorReporter* error_reporter = &micro_error_reporter;
  const tflite::Model* model = nullptr;
  tflite::MicroInterpreter* interpreter = nullptr;
  TfLiteTensor* input = nullptr;
  TfLiteTensor* output = nullptr;
  uint8_t tensor_arena[kTensorArenaSize];
}

// BLE HID UUIDs
#define HID_SERVICE_UUID "1812"
#define HID_REPORT_UUID "2A4D"
#define HID_REPORT_MAP_UUID "2A4B"
#define HID_INFORMATION_UUID "2A4A"
#define HID_CONTROL_POINT_UUID "2A4C"

// HID Report Descriptor for a Keyboard
const uint8_t REPORT_MAP[] = {
  0x05, 0x01,  0x09, 0x06,  0xA1, 0x01, 0x05, 0x07, 0x19, 0xE0, 0x29, 0xE7, 
  0x15, 0x00, 0x25, 0x01, 0x75, 0x01, 0x95, 0x08, 0x81, 0x02, 0x95, 0x01, 
  0x75, 0x08, 0x81, 0x03, 0x95, 0x06, 0x75, 0x08, 0x15, 0x00, 0x25, 0x65,  
  0x05, 0x07, 0x19, 0x00, 0x29, 0x65, 0x81, 0x00, 0xC0 
};

BLEService hidService(HID_SERVICE_UUID);
BLECharacteristic hidReportCharacteristic(HID_REPORT_UUID, BLERead | BLENotify, 8);
BLECharacteristic hidReportMapCharacteristic(HID_REPORT_MAP_UUID, BLERead, sizeof(REPORT_MAP));
BLECharacteristic hidInformationCharacteristic(HID_INFORMATION_UUID, BLERead, 4);
BLECharacteristic hidControlPointCharacteristic(HID_CONTROL_POINT_UUID, BLEWriteWithoutResponse, 1);

void setup() {
  Serial.begin(9600);
  while (!Serial);

  initializeShield();

  if (!Camera.begin(QCIF, RGB565, 1, OV7675)) {
    Serial.println("Failed to initialize camera");
    while (1);
  }
  bytesPerFrame = Camera.width() * Camera.height() * Camera.bytesPerPixel();

  //Serial.println("Welcome to the OV7675 capture program\n");
  Serial.println("Press the button to take an image. An image is taken for 3 seconds after pressing.");
  //Serial.println("Wait pressing again until you see the '.' delimiter.");

  model = tflite::GetModel(model_data);
  if (model == nullptr) {
    Serial.println("Failed to get model from model_data.");
    while (1);
  }

  if (model->version() != TFLITE_SCHEMA_VERSION) {
    Serial.print("Model provided is schema version ");
    Serial.print(model->version());
    Serial.print(", not equal to supported version ");
    Serial.println(TFLITE_SCHEMA_VERSION);
    while (1);
  }

  Serial.println("Model schema version is correct.");

  static tflite::AllOpsResolver resolver;

  static tflite::MicroInterpreter static_interpreter(model, resolver, tensor_arena, kTensorArenaSize, error_reporter);
  interpreter = &static_interpreter;

  TfLiteStatus allocate_status = interpreter->AllocateTensors();
  if (allocate_status != kTfLiteOk) {
    Serial.print("AllocateTensors() failed with status: ");
    Serial.println(allocate_status);
    Serial.print("Arena used bytes: ");
    Serial.println(interpreter->arena_used_bytes());
    while (1);
  }

  Serial.println("AllocateTensors() succeeded.");
  Serial.print("Arena used bytes: ");
  Serial.println(interpreter->arena_used_bytes());

  input = interpreter->input(0);
  output = interpreter->output(0);

  if (!BLE.begin()) {
    Serial.println("Starting BLE failed!");
    while (1);
  }
  Serial.println("BLE started.");

  BLE.setLocalName("Nano 33 BLE HID Keyboard");
  BLE.setAdvertisedService(hidService);
  hidService.addCharacteristic(hidReportCharacteristic);
  hidService.addCharacteristic(hidReportMapCharacteristic);
  hidService.addCharacteristic(hidInformationCharacteristic);
  hidService.addCharacteristic(hidControlPointCharacteristic);
  BLE.addService(hidService);

  hidReportMapCharacteristic.writeValue(REPORT_MAP, sizeof(REPORT_MAP));
  uint8_t hidInfo[4] = {0x11, 0x01, 0x00, 0x02};
  hidInformationCharacteristic.writeValue(hidInfo, sizeof(hidInfo));

  BLE.advertise();
  Serial.println("Bluetooth device active, waiting for connections...");
}

void loop() {
  BLEDevice central = BLE.central();

  if (central) {
    Serial.print("Connected to central: ");
    Serial.println(central.address());

    while (central.connected()) {
      bool clicked = readShieldButton();
      if (clicked) {
        if (!captureFlag) {
          captureFlag = true;
        }
      }

      if (captureFlag) {
        captureFlag = false;
        Camera.readFrame(image);
        delay(3000);

        uint8_t input_image[image_width * image_height * num_channels];
        preprocessImage(image, input_image, 176, 144, image_width, image_height);

        for (int i = 0; i < image_width * image_height * num_channels; i++) {
          input->data.uint8[i] = input_image[i];
        }

        TfLiteStatus invoke_status = interpreter->Invoke();
        if (invoke_status != kTfLiteOk) {
          Serial.println("Invoke failed with status: " + String(invoke_status));
          return;
        }

        //Takes the index from the output array
        uint8_t max_value = 0;
        int8_t predicted_index = -1;
        for (int i = 0; i < output->dims->data[1]; i++) {
          if (output->data.uint8[i] > max_value) {
            max_value = output->data.uint8[i];
            predicted_index = i;
          }
        }

        //takes a letter from the corresponding index
        const char* class_to_char = "abcdefghijklmnopqrstuvwxyz";
        if (predicted_index >= 0 && predicted_index < strlen(class_to_char)) {
          char predicted_letter = class_to_char[predicted_index];

          Serial.print("Predicted letter: ");
          Serial.println(predicted_letter);

          sendKeyPress(0x00, predicted_letter - 'a' + 4);
        } else {
          Serial.println("Predicted letter: Invalid index");
        }
        Serial.println('.');
      }
    }

    Serial.print("Disconnected from central: ");
    Serial.println(central.address());
  }
}

//converts the incoming image into grayscale
void preprocessImage(byte* source, uint8_t* dest, int src_width, int src_height, int dest_width, int dest_height) {
  for (int y = 0; y < dest_height; y++) {
    for (int x = 0; x < dest_width; x++) {
      int src_x = x * src_width / dest_width;
      int src_y = y * src_height / dest_height;
      int src_index = (src_y * src_width + src_x) * 2;

      uint16_t pixel = (source[src_index] << 8) | source[src_index + 1];
      uint8_t r = (pixel & 0xF800) >> 8;
      uint8_t g = (pixel & 0x07E0) >> 3;
      uint8_t b = (pixel & 0x001F) << 3;

      uint8_t gray = (r * 299 + g * 587 + b * 114) / 1000;
      dest[y * dest_width + x] = gray;
    }
  }
}

//sends the predicted key over a bluetooth connection
void sendKeyPress(uint8_t modifier, uint8_t key) {
  uint8_t report[8] = {modifier, 0x00, key, 0x00, 0x00, 0x00, 0x00, 0x00};
  hidReportCharacteristic.writeValue(report, sizeof(report));
  delay(200);
  uint8_t release[8] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  hidReportCharacteristic.writeValue(release, sizeof(release));
}
