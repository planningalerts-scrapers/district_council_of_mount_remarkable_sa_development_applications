// Parses the development applications at the South Australian District Council of Mount Remarkable
// web site and places them in a database.
//
// Michael Bone
// 9th March 2019
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const fs = require("fs");
const cheerio = require("cheerio");
const request = require("request-promise-native");
const sqlite3 = require("sqlite3");
const urlparser = require("url");
const moment = require("moment");
const pdfjs = require("pdfjs-dist");
const didyoumean2_1 = require("didyoumean2"), didyoumean = didyoumean2_1;
sqlite3.verbose();
const DevelopmentApplicationsUrl = "https://www.mtr.sa.gov.au/documents/district-council-of-mount-remarkable6";
const CommentUrl = "mailto:postmaster@mtr.sa.gov.au";
// All valid street names, street suffixes, suburb names and hundred names.
let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;
// Two points that are less than the tolerance apart will be considered the same point.
const Tolerance = 3;
// Sets up an sqlite database.
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}
// Inserts a row in the database if the row does not already exist.
async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or replace into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function (error, row) {
            if (error) {
                console.error(error);
                reject(error);
            }
            else {
                console.log(`    Saved application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" to the database.`);
                sqlStatement.finalize(); // releases any locks
                resolve(row);
            }
        });
    });
}
// Constructs a rectangle based on the intersection of the two specified rectangles.
function intersectRectangles(rectangle1, rectangle2) {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}
// Finds the intersection point of two lines.
function intersectLines(line1, line2) {
    if ((line1.x1 === line1.x2 && line1.y1 === line1.y2) || (line2.x1 === line2.x2 && line2.y1 === line2.y2))
        return undefined; // ignore zero length lines
    let denominator = (line2.y2 - line2.y1) * (line1.x2 - line1.x1) - (line1.x2 - line1.x1) * (line1.y2 - line1.y1);
    if (denominator === 0)
        return undefined; // ignore parallel lines
    let distance1 = ((line2.x2 - line2.x1) * (line1.y1 - line2.y1) - (line2.y2 - line2.y1) * (line1.x1 - line2.x1)) / denominator;
    let distance2 = ((line1.x2 - line1.x1) * (line1.y1 - line2.y1) - (line1.y2 - line1.y1) * (line1.x1 - line2.x1)) / denominator;
    if (distance1 < 0 || distance1 > 1 || distance2 < 0 || distance2 > 1) // check that the intersection is within the line segements
        return undefined;
    let x = line1.x1 + distance1 * (line1.x2 - line1.x1);
    let y = line1.y1 + distance1 * (line1.y2 - line1.y1);
    return { x: x, y: y };
}
// Rotates a rectangle 90 degrees clockwise about the origin.
function rotate90Clockwise(rectangle) {
    let x = -(rectangle.y + rectangle.height);
    let y = rectangle.x;
    let width = rectangle.height;
    let height = rectangle.width;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
}
// Rotates a rectangle 90 degrees anti-clockwise about the origin.
function rotate90AntiClockwise(rectangle) {
    let x = rectangle.y;
    let y = -(rectangle.x + rectangle.width);
    let width = rectangle.height;
    let height = rectangle.width;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
}
// Calculates the fraction of an element that lies within a cell (as a percentage).  For example,
// if a quarter of the specifed element lies within the specified cell then this would return 25.
function getPercentageOfElementInCell(element, cell) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersectRectangles(cell, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}
// Calculates the area of a rectangle.
function getArea(rectangle) {
    return rectangle.width * rectangle.height;
}
// Gets the percentage of horizontal overlap between two rectangles (0 means no overlap and 100
// means 100% overlap).
function getHorizontalOverlapPercentage(rectangle1, rectangle2) {
    if (rectangle1 === undefined || rectangle2 === undefined)
        return 0;
    let startX1 = rectangle1.x;
    let endX1 = rectangle1.x + rectangle1.width;
    let startX2 = rectangle2.x;
    let endX2 = rectangle2.x + rectangle2.width;
    if (startX1 >= endX2 || endX1 <= startX2 || rectangle1.width === 0 || rectangle2.width === 0)
        return 0;
    let intersectionWidth = Math.min(endX1, endX2) - Math.max(startX1, startX2);
    let unionWidth = Math.max(endX1, endX2) - Math.min(startX1, startX2);
    return (intersectionWidth * 100) / unionWidth;
}
// Examines all the lines in a page of a PDF and constructs cells (ie. rectangles) based on those
// lines.
async function parseCells(page, useRectangles) {
    let operators = await page.getOperatorList();
    // Find the lines.  Each line is actually constructed using a rectangle with a very short
    // height or a very narrow width.
    let lines = [];
    let previousRectangle = undefined;
    let transformStack = [];
    let transform = [1, 0, 0, 1, 0, 0];
    transformStack.push(transform);
    for (let index = 0; index < operators.fnArray.length; index++) {
        let argsArray = operators.argsArray[index];
        // The following lists all drawing and text instructions in the PDF (this is useful for
        // troubleshooting purposes).
        console.log(`${Object.entries(pdfjs.OPS).find(pair => pair[1] === operators.fnArray[index])} ${argsArray}`);
        if (operators.fnArray[index] === pdfjs.OPS.restore)
            transform = transformStack.pop();
        else if (operators.fnArray[index] === pdfjs.OPS.save)
            transformStack.push(transform);
        else if (operators.fnArray[index] === pdfjs.OPS.transform)
            transform = pdfjs.Util.transform(transform, argsArray);
        else if (operators.fnArray[index] === pdfjs.OPS.constructPath) {
            if (useRectangles) { // older PDFs use this approach to construct lines
                let argumentIndex = 0;
                for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                    if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo) // moveTo = 13
                        argumentIndex += 2;
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo) // lineTo = 14
                        argumentIndex += 2;
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.rectangle) { // rectangle = 19
                        let x1 = argsArray[1][argumentIndex++];
                        let y1 = argsArray[1][argumentIndex++];
                        let width = argsArray[1][argumentIndex++];
                        let height = argsArray[1][argumentIndex++];
                        let x2 = x1 + width;
                        let y2 = y1 + height;
                        [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                        [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                        width = x2 - x1;
                        height = y2 - y1;
                        previousRectangle = { x: x1, y: y1, width: width, height: height };
                    }
                }
            }
            else { // newer PDFs use this approach to construct lines
                let x1 = undefined;
                let y1 = undefined;
                let x2 = undefined;
                let y2 = undefined;
                let argumentIndex = 0;
                for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                    if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo) { // moveTo = 13
                        x1 = argsArray[1][argumentIndex++];
                        y1 = argsArray[1][argumentIndex++];
                    }
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo) { // lineTo = 14
                        if ((argumentIndex % 8) === 4) { // the right-most, bottom-most index (ie. the diagonally opposite corner of the rectangle)
                            x2 = argsArray[1][argumentIndex++];
                            y2 = argsArray[1][argumentIndex++];
                        }
                        else {
                            argumentIndex += 2;
                        }
                    }
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.closePath) { // closePath = 18
                        if (x1 === undefined || y1 === undefined)
                            console.log("    Ignoring the constructed path because the top, left co-ordinate is undefined.");
                        else if (x2 === undefined || y2 === undefined)
                            console.log(`    Ignoring the constructed path because the bottom, right co-ordinate is undefined (but the top, left co-ordindate is [${x1}, ${y1}]).`);
                        else {
                            [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                            [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                            let width = x2 - x1;
                            let height = y2 - y1;
                            if (width < 0)
                                lines.push({ x: x1 + width, y: y1, width: Math.abs(width), height: height });
                            else
                                lines.push({ x: x1, y: y1, width: width, height: height });
                            x1 = undefined;
                            y1 = undefined;
                            x2 = undefined;
                            y2 = undefined;
                        }
                    }
                }
            }
        }
        else if (useRectangles && previousRectangle !== undefined && (operators.fnArray[index] === pdfjs.OPS.fill || operators.fnArray[index] === pdfjs.OPS.eoFill)) {
            lines.push(previousRectangle);
            previousRectangle = undefined;
        }
        //        } else if (!useRectangles && previousRectangle !== undefined && operators.fnArray[index] === pdfjs.OPS.endPath) {
        //            lines.push(previousRectangle);
        //            previousRectangle = undefined;
        //        }
    }
    console.log(`Found ${lines.length} line(s).`);
    for (let line of lines)
        console.log(`DrawRectangle(e.Graphics, ${line.x}f, ${line.y}f, ${line.width}f, ${line.height}f);  // line segment`);
    // Determine all the horizontal lines and vertical lines that make up the grid.  The following
    // is careful to ignore the short lines and small rectangles that could make up vector images
    // outside of the grid (such as a logo).  Otherwise these short lines would cause problems due
    // to the additional cells that they would cause to be constructed later.
    let horizontalLines = [];
    let verticalLines = [];
    for (let line of lines) {
        if (line.height <= Tolerance && line.width >= 10) // a horizontal line
            horizontalLines.push(line);
        else if (line.width <= Tolerance && line.height >= 10) // a vertical line
            verticalLines.push(line);
    }
    let verticalLineComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
    verticalLines.sort(verticalLineComparer);
    console.log(`Found ${verticalLines.length} vertical line(s).`);
    let horizontalLineComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    horizontalLines.sort(horizontalLineComparer);
    console.log(`Found ${horizontalLines.length} horizontal line(s).`);
    // Add the start and end points of all lines.
    let points = [];
    for (let line of horizontalLines) {
        let point = { x: line.x, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
        point = { x: line.x + line.width, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
    }
    for (let line of verticalLines) {
        let point = { x: line.x, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
        point = { x: line.x, y: line.y + line.height };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
    }
    // Find all intersection points.
    for (let verticalLine of verticalLines) {
        for (let horizontalLine of horizontalLines) {
            let point = intersectLines({ x1: horizontalLine.x, y1: horizontalLine.y, x2: horizontalLine.x + horizontalLine.width, y2: horizontalLine.y }, { x1: verticalLine.x, y1: verticalLine.y, x2: verticalLine.x, y2: verticalLine.y + verticalLine.height });
            if (point !== undefined && !points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
                points.push(point); // add the intersection point
        }
    }
    // Construct cells based on the grid of points.
    let cells = [];
    for (let point of points) {
        // Find the next closest point in the X direction (moving across horizontally with
        // approximately the same Y co-ordinate).
        let closestRightPoint = points.reduce(((previous, current) => (Math.abs(current.y - point.y) < Tolerance && current.x > point.x && (previous === undefined || (current.x - point.x < previous.x - point.x))) ? current : previous), undefined);
        // Find the next closest point in the Y direction (moving down vertically with
        // approximately the same X co-ordinate).
        let closestDownPoint = points.reduce(((previous, current) => (Math.abs(current.x - point.x) < Tolerance && current.y > point.y && (previous === undefined || (current.y - point.y < previous.y - point.y))) ? current : previous), undefined);
        // Construct a rectangle from the found points.
        if (closestRightPoint !== undefined && closestDownPoint !== undefined)
            cells.push({ elements: [], x: point.x, y: point.y, width: closestRightPoint.x - point.x, height: closestDownPoint.y - point.y });
    }
    // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.
    let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
    cells.sort(cellComparer);
    return cells;
}
// Parses the text elements from a page of a PDF.
async function parseElements(page) {
    let textContent = await page.getTextContent();
    // Find all the text elements.
    let elements = textContent.items.map(item => {
        let transform = item.transform;
        // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
        // exaggerated).  The problem seems to be that the height value is too large in some
        // PDFs.  Provide an alternative, more accurate height value by using a calculation
        // based on the transform matrix.
        let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
        let x = transform[4];
        let y = transform[5];
        let width = item.width;
        let height = workaroundHeight;
        return { text: item.str, x: x, y: y, width: width, height: height };
    });
    return elements;
}
// Formats (and corrects) an address.
function formatAddress(applicationNumber, address) {
    address = address.trim().replace(/[-–]+$/, "").replace(/\s\s+/g, " ").trim(); // remove trailing dashes and multiple white space characters
    if (address.replace(/[\s,0-]/g, "") === "" || address.startsWith("No Residential Address")) // ignores addresses such as "0 0, 0" and "-"
        return "";
    // Remove the comma in house numbers larger than 1000.  For example, the following addresses:
    //
    //     4,665 Princes HWY MENINGIE 5264
    //     11,287 Princes HWY SALT CREEK 5264
    //
    // would be converted to the following:
    //
    //     4665 Princes HWY MENINGIE 5264
    //     11287 Princes HWY SALT CREEK 5264
    if (/^\d,\d\d\d/.test(address))
        address = address.substring(0, 1) + address.substring(2);
    else if (/^\d\d,\d\d\d/.test(address))
        address = address.substring(0, 2) + address.substring(3);
    let tokens = address.split(" ");
    let postCode = undefined;
    let token = tokens.pop();
    if (token === undefined)
        return address;
    if (/^\d\d\d\d$/.test(token))
        postCode = token;
    else
        tokens.push(token);
    // Ensure that a state code is added before the post code if a state code is not present.
    let state = "SA";
    token = tokens.pop();
    if (token === undefined)
        return address;
    if (["ACT", "NSW", "NT", "QLD", "SA", "TAS", "VIC", "WA"].includes(token.toUpperCase()))
        state = token.toUpperCase();
    else
        tokens.push(token);
    // Construct a fallback address to be used if the suburb name cannot be determined later.
    let fallbackAddress = (postCode === undefined) ? address : [...tokens, state, postCode].join(" ").trim();
    // Pop tokens from the end of the array until a valid suburb name is encountered (allowing
    // for a few spelling errors).  Note that this starts by examining for longer matches
    // (consisting of four tokens) before examining shorter matches.  This approach ensures
    // that the following address:
    //
    //     2,800 Woods Well RD COLEBATCH 5266
    //
    // is correctly converted to the following address:
    //
    //     2800 WOODS WELL ROAD, COLEBATCH SA 5266
    //
    // rather than (incorrectly) to the following address (notice that the street name has "BELL"
    // instead of "WELL" because there actually is a street named "BELL ROAD").
    //
    //     2800 Woods BELL ROAD, COLEBATCH SA 5266
    //
    // This also allows for addresses that contain hundred names such as the following:
    //
    //     Sec 26 Hd Palabie
    //     Lot no 1, Standley Road, Sect 16, Hundred of Pygery
    let suburbName = undefined;
    let hasHundredName = false;
    for (let index = 4; index >= 1; index--) {
        let tryHundredName = tokens.slice(-index).join(" ").toUpperCase();
        if (tryHundredName.startsWith("HD OF ") || tryHundredName.startsWith("HUNDRED OF") || tryHundredName.startsWith("HD ") || tryHundredName.startsWith("HUNDRED ")) {
            tryHundredName = tryHundredName.replace(/^HD OF /, "").replace(/^HUNDRED OF /, "").replace(/^HD /, "").replace(/^HUNDRED /, "").trim();
            let hundredNameMatch = didyoumean2_1.default(tryHundredName, Object.keys(HundredNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
            if (hundredNameMatch !== null) {
                hasHundredName = true;
                let suburbNames = HundredNames[hundredNameMatch];
                if (suburbNames.length === 1) { // if a unique suburb exists for the hundred then use that suburb
                    suburbName = SuburbNames[suburbNames[0]];
                    tokens.splice(-index, index); // remove elements from the end of the array
                }
                break;
            }
        }
    }
    // Only search for a suburb name if there was no hundred name (because a suburb name is
    // unlikely to appear before a hundred name).
    if (!hasHundredName) {
        for (let index = 4; index >= 1; index--) {
            let trySuburbName = tokens.slice(-index).join(" ");
            let suburbNameMatch = didyoumean2_1.default(trySuburbName, Object.keys(SuburbNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
            if (suburbNameMatch !== null) {
                suburbName = SuburbNames[suburbNameMatch];
                tokens.splice(-index, index); // remove elements from the end of the array           
                break;
            }
        }
    }
    // Expand any street suffix (for example, this converts "ST" to "STREET").
    token = tokens.pop();
    if (token !== undefined) {
        token = token.trim().replace(/,+$/, "").trim(); // removes trailing commas
        let streetSuffix = StreetSuffixes[token.toUpperCase()];
        if (streetSuffix === undefined)
            streetSuffix = Object.values(StreetSuffixes).find(streetSuffix => streetSuffix === token.toUpperCase()); // the street suffix is already expanded
        if (streetSuffix === undefined)
            tokens.push(token); // unrecognised street suffix
        else
            tokens.push(streetSuffix); // add back the expanded street suffix
    }
    // Pop tokens from the end of the array until a valid street name is encountered (allowing
    // for a few spelling errors).  Similar to the examination of suburb names, this examines
    // longer matches before examining shorter matches (for the same reason).
    let streetName = undefined;
    for (let index = 5; index >= 1; index--) {
        let tryStreetName = tokens.slice(-index).join(" ").trim().replace(/,+$/, "").trim(); // allows for commas after the street name
        let streetNameMatch = didyoumean2_1.default(tryStreetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
        if (streetNameMatch !== null) {
            streetName = streetNameMatch;
            let suburbNames = StreetNames[streetNameMatch];
            tokens.splice(-index, index); // remove elements from the end of the array           
            // If the suburb was not determined earlier then attempt to obtain the suburb based
            // on the street (ie. if there is only one suburb associated with the street).  For
            // example, this would automatically add the suburb to "22 Jefferson CT 5263",
            // producing the address "22 JEFFERSON COURT, WELLINGTON EAST SA 5263".
            if (suburbName === undefined && suburbNames.length === 1)
                suburbName = SuburbNames[suburbNames[0]];
            break;
        }
    }
    // If a post code was included in the original address then use it to override the post code
    // included in the suburb name (because the post code in the original address is more likely
    // to be correct).
    if (postCode !== undefined && suburbName !== undefined)
        suburbName = suburbName.replace(/\s+\d\d\d\d$/, " " + postCode);
    // Do not allow an address that does not have a suburb name.
    if (suburbName === undefined) {
        console.log(`Ignoring the development application "${applicationNumber}" because a suburb name could not be determined for the address: ${address}`);
        return "";
    }
    // Reconstruct the address with a comma between the street address and the suburb.
    if (suburbName === undefined || suburbName.trim() === "")
        address = fallbackAddress;
    else {
        if (streetName !== undefined && streetName.trim() !== "")
            tokens.push(streetName);
        let streetAddress = tokens.join(" ").trim().replace(/,+$/, "").trim(); // removes trailing commas
        address = streetAddress + (streetAddress === "" ? "" : ", ") + suburbName;
    }
    // Ensure that the address includes the state "SA".
    if (address !== "" && !/\bSA\b/g.test(address))
        address += " SA";
    return address;
}
// Parses a PDF document.
async function parsePdf(url, shouldRotate) {
    console.log(`Reading development applications from ${url}.`);
    let developmentApplications = [];
    // Read the PDF.
    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.
    let applicationNumberHeadingCell = undefined;
    let receivedDateHeadingCell = undefined;
    let addressHeadingCell = undefined;
    let descriptionHeadingCell = undefined;
    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    for (let pageIndex = 0; pageIndex < pdf.numPages; pageIndex++) {
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        // Construct cells (ie. rectangles) based on the horizontal and vertical line segments
        // in the PDF page.
        let cells = await parseCells(page, false);
        // Construct elements based on the text in the PDF page.
        let elements = await parseElements(page);
        // for (let cell of cells)
        //     console.log(`DrawRectangle(e.Graphics, ${cell.x}f, ${cell.y}f, ${cell.width}f, ${cell.height}f);`);
        for (let element of elements)
            console.log(`DrawText(e.Graphics, "${element.text.replace(/\"/g, "\"\"")}", ${element.x}f, ${element.y}f, ${element.width}f, ${element.height}f);`);
        if (page.rotate !== 0) // degrees
            console.log(`Page is rotated ${page.rotate}°.`);
        if (shouldRotate) {
            // Experimentally determined that the following rotation and translation correctly
            // aligns the grid lines with the text elements in some PDFs.
            console.log("Retrying with a rotation of 90°.");
            let viewport = await page.getViewport(1.0);
            for (let cell of cells) {
                rotate90AntiClockwise(cell);
                cell.y = cell.y + viewport.height; // experimentally determined translation
            }
        }
        // The co-ordinate system used in a PDF is typically "upside down" so invert the
        // co-ordinates (and so this makes the subsequent logic easier to understand).
        for (let cell of cells)
            cell.y = -(cell.y + cell.height);
        for (let element of elements)
            element.y = -(element.y + element.height);
        if (page.rotate !== 0) // degrees
            console.log(`Page is rotated ${page.rotate}°.`);
        if (page.rotate === 90) { // degrees
            for (let cell of cells)
                rotate90Clockwise(cell);
            for (let element of elements) {
                rotate90Clockwise(element);
                [element.y, element.width, element.height] = [element.y - element.width, element.height, element.width]; // artificial adjustment (based on experimentation)
            }
        }
        // Sort the elements by approximate Y co-ordinate and then by X co-ordinate.
        let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        cells.sort(cellComparer);
        console.log(`    Cell count: ${cells.length}`);
        // Sort the text elements by approximate Y co-ordinate and then by X co-ordinate.
        let elementComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        elements.sort(elementComparer);
        console.log(`    Element count: ${elements.length}`);
        // Allocate each element to an "owning" cell.
        let ownedElementCount = 0;
        for (let element of elements) {
            let ownerCell = cells.find(cell => getPercentageOfElementInCell(element, cell) > 50); // at least 50% of the element must be within the cell deemed to be the owner
            if (ownerCell !== undefined) {
                ownerCell.elements.push(element);
                ownedElementCount++;
            }
        }
        console.log(`    Elements owned by cells count: ${ownedElementCount}`);
        // Group the cells into rows.
        let rows = [];
        for (let cell of cells) {
            let row = rows.find(row => Math.abs(row[0].y - cell.y) < Tolerance); // approximate Y co-ordinate match
            if (row === undefined)
                rows.push([cell]); // start a new row
            else
                row.push(cell); // add to an existing row
        }
        // Check that there is at least one row (even if it is just the heading row).
        if (rows.length === 0) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because no rows were found (based on the grid).  Elements: ${elementSummary}`);
            continue;
        }
        // Ensure the rows are sorted by Y co-ordinate and that the cells in each row are sorted
        // by X co-ordinate (this is really just a safety precaution because the earlier sorting
        // of cells in the parseCells function should have already ensured this).
        let rowComparer = (a, b) => (a[0].y > b[0].y) ? 1 : ((a[0].y < b[0].y) ? -1 : 0);
        rows.sort(rowComparer);
        let rowCellComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
        for (let row of rows)
            row.sort(rowCellComparer);
        // Find the heading cells.
        if (applicationNumberHeadingCell === undefined) {
            applicationNumberHeadingCell = cells.find(cell => /^(developmentnumber|developmentno\.|appno)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            receivedDateHeadingCell = cells.find(cell => /^(dateofapplication|dateofregistration|dateregistered)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            addressHeadingCell = cells.find(cell => /^(propertyaddress|locationofdevelopment)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            descriptionHeadingCell = cells.find(cell => /^(natureofdevelopment|descriptionofdev)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
        }
        if (applicationNumberHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "Development Number", Development No." or "App No" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }
        if (addressHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "Property Address" or "Location of Development" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }
        // Try to extract a development application from each row (some rows, such as the heading
        // row, will not actually contain a development application).
        for (let row of rows) {
            let applicationNumberCell = row.find(cell => getHorizontalOverlapPercentage(cell, applicationNumberHeadingCell) > 90);
            let receivedDateCell = row.find(cell => getHorizontalOverlapPercentage(cell, receivedDateHeadingCell) > 90);
            let addressCell = row.find(cell => getHorizontalOverlapPercentage(cell, addressHeadingCell) > 90);
            let descriptionCell = row.find(cell => getHorizontalOverlapPercentage(cell, descriptionHeadingCell) > 90);
            // Construct the application number.
            if (applicationNumberCell === undefined) {
                let rowSummary = row.map(cell => `[${cell.elements.map(element => `(${element.text})`).join("")}]`).join("");
                console.log(`No application number was found on the row: ${rowSummary}`);
                continue;
            }
            let applicationNumber = applicationNumberCell.elements.map(element => element.text).join("").trim();
            if (!/[0-9]+\/[0-9]+\/[0-9]+/.test(applicationNumber)) { // an application number must be present, for example, "690/006/15"
                console.log(`Ignoring "${applicationNumber}" because it is not formatted as an application number.`);
                continue;
            }
            console.log(`Found development application ${applicationNumber}.`);
            // Construct the address.
            if (addressCell === undefined) {
                console.log(`Ignoring the development application "${applicationNumber}" because it has no address cell.`);
                continue;
            }
            let address = addressCell.elements.map(element => element.text).join(" ").replace(/\s\s+/g, " ").trim();
            address = formatAddress(applicationNumber, address);
            if (address === "") {
                console.log(`Ignoring the development application "${applicationNumber}" because it has no address.`);
                continue;
            }
            // Construct the description.
            let description = "";
            if (descriptionCell !== undefined)
                description = descriptionCell.elements.map(element => element.text).join(" ").replace(/\s\s+/g, " ").trim();
            // Construct the received date.
            let receivedDate = moment.invalid();
            if (receivedDateCell !== undefined && receivedDateCell.elements.length > 0)
                receivedDate = moment(receivedDateCell.elements.map(element => element.text).join("").replace(/\s\s+/g, " ").trim(), "D/MM/YYYY", true);
            developmentApplications.push({
                applicationNumber: applicationNumber,
                address: address,
                description: ((description === "") ? "No Description Provided" : description),
                informationUrl: url,
                commentUrl: CommentUrl,
                scrapeDate: moment().format("YYYY-MM-DD"),
                receivedDate: receivedDate.isValid() ? receivedDate.format("YYYY-MM-DD") : ""
            });
        }
    }
    return developmentApplications;
}
// Gets a random integer in the specified range: [minimum, maximum).
function getRandom(minimum, maximum) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}
// Pauses for the specified number of milliseconds.
function sleep(milliseconds) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}
// Parses the development applications.
async function main() {
    // Ensure that the database exists.
    let database = await initializeDatabase();
    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.
    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName); // several suburbs may exist for the same street name
    }
    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }
    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }
    HundredNames = {};
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let hundredNameTokens = line.toUpperCase().split(",");
        HundredNames[hundredNameTokens[0].trim()] = hundredNameTokens[1].trim().split(";");
    }
    // Read the main page of development applications.
    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);
    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    let pdfUrls = [];
    for (let element of $("h4 a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href;
        if (pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl)) // avoid duplicates
                pdfUrls.unshift(pdfUrl);
    }
    // Always parse the most recent PDF file and randomly select one other PDF file to parse.
    if (pdfUrls.length === 0) {
        console.log("No PDF URLs were found on the page.");
        return;
    }
    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);
    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).
    let selectedPdfUrls = [];
    selectedPdfUrls.push(pdfUrls.pop());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();
    console.log("Hard-coded the PDF for testing purposes.");
    selectedPdfUrls = ["https://www.mtr.sa.gov.au/__data/assets/pdf_file/0035/479393/6.-June-2020.pdf"];
    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl, false);
        //        if (developmentApplications.length === 0)
        //            developmentApplications = await parsePdf(pdfUrl, true);
        console.log(`Parsed ${developmentApplications.length} development ${(developmentApplications.length == 1) ? "application" : "applications"} from document: ${pdfUrl}`);
        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).
        if (global.gc)
            global.gc();
        console.log("Saving development applications to the database.");
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}
main().then(() => console.log("Complete.")).catch(error => console.error(error));
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NyYXBlci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNjcmFwZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsbUdBQW1HO0FBQ25HLDBDQUEwQztBQUMxQyxFQUFFO0FBQ0YsZUFBZTtBQUNmLGlCQUFpQjtBQUVqQixZQUFZLENBQUM7O0FBRWIseUJBQXlCO0FBQ3pCLG1DQUFtQztBQUNuQyxrREFBa0Q7QUFDbEQsbUNBQW1DO0FBQ25DLGlDQUFpQztBQUNqQyxpQ0FBaUM7QUFDakMsb0NBQW9DO0FBQ3BDLHlFQUFzRDtBQUV0RCxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7QUFFbEIsTUFBTSwwQkFBMEIsR0FBRywyRUFBMkUsQ0FBQztBQUMvRyxNQUFNLFVBQVUsR0FBRyxpQ0FBaUMsQ0FBQztBQUlyRCwyRUFBMkU7QUFFM0UsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDO0FBQ3ZCLElBQUksY0FBYyxHQUFHLElBQUksQ0FBQztBQUMxQixJQUFJLFdBQVcsR0FBRyxJQUFJLENBQUM7QUFDdkIsSUFBSSxZQUFZLEdBQUcsSUFBSSxDQUFDO0FBRXhCLHVGQUF1RjtBQUV2RixNQUFNLFNBQVMsR0FBRyxDQUFDLENBQUM7QUFFcEIsOEJBQThCO0FBRTlCLEtBQUssVUFBVSxrQkFBa0I7SUFDN0IsT0FBTyxJQUFJLE9BQU8sQ0FBQyxDQUFDLE9BQU8sRUFBRSxNQUFNLEVBQUUsRUFBRTtRQUNuQyxJQUFJLFFBQVEsR0FBRyxJQUFJLE9BQU8sQ0FBQyxRQUFRLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDbkQsUUFBUSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUU7WUFDcEIsUUFBUSxDQUFDLEdBQUcsQ0FBQyw4TEFBOEwsQ0FBQyxDQUFDO1lBQzdNLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUN0QixDQUFDLENBQUMsQ0FBQztJQUNQLENBQUMsQ0FBQyxDQUFDO0FBQ1AsQ0FBQztBQUVELG1FQUFtRTtBQUVuRSxLQUFLLFVBQVUsU0FB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LEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0lBQ2hILElBQUksV0FBVyxLQUFLLENBQUM7UUFDakIsT0FBTyxTQUFTLENBQUMsQ0FBRSx3QkFBd0I7SUFFL0MsSUFBSSxTQUFTLEdBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEdBQUcsV0FBVyxDQUFDO0lBQzlILElBQUksU0FBUyxHQUFHLENBQUMsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsQ0FBQyxHQUFHLFdBQVcsQ0FBQztJQUM5SCxJQUFJLFNBQVMsR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUcsMkRBQTJEO1FBQzlILE9BQU8sU0FBUyxDQUFDO0lBRXJCLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQyxFQUFFLEdBQUcsU0FBUyxHQUFHLENBQUMsS0FB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Q0FBQyxDQUFDO0lBRW5FLDZDQUE2QztJQUU3QyxJQUFJLE1BQU0sR0FBWSxFQUFFLENBQUM7SUFFekIsS0FBSyxJQUFJLElBQUksSUFBSSxlQUFlLEVBQUU7UUFDOUIsSUFBSSxLQUFLLEdBQUcsRUFBRSxDQUFDLEVBQUUsSUFBSSxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUUsSUFBSSxDQUFDLENBQUMsRUFBRSxDQUFDO1FBQ3JDLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxHQUFHLFVBQVUsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsQ0FBQyxHQUFHLFVBQVUsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsU0FBUyxJQUFJLENBQUMsQ0FBQztZQUMxRyxNQUFNLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ3ZCLEtBQUssR0FBRyxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxLQUFLLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUM5QyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLFNBQVMsSUFBSSxDQUFDLENBQUM7WUFDMUcsTUFBTSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztLQUMxQjtJQUVELEtBQUssSUFBSSxJQUFJLElBQUksYUFBYSxFQUFFO1FBQzVCLElBQUksS0FBSyxHQUFHLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUNyQyxJ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